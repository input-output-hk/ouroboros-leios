/*
 * scheduler_bridge.c — Embeds CPython and bridges between the C node's
 * event loop and FetchScheduler.py's step() function.
 *
 * The C node calls scheduler_*() functions at protocol event points.
 * Each call:
 *   1. Builds a Python event object from C data.
 *   2. Calls FetchScheduler.step(state, event).
 *   3. Iterates the returned action list and executes each action
 *      (send MSG_REQUEST, send MSG_CANCEL_CHUNK, or arm a timerfd).
 */

#include <Python.h>
#include "scheduler_bridge.h"
#include "node.h"

#include <sys/timerfd.h>
#include <netinet/tcp.h>

/* ---------------------------------------------------------------------------
 * Python module and class references (cached at init)
 * ------------------------------------------------------------------------ */

static PyObject *py_module;
static PyObject *py_state;     /* SchedulerState instance */
static PyObject *py_step_fn;   /* FetchScheduler.step */

/* Event constructors */
static PyObject *cls_ManifestReceived;
static PyObject *cls_OfferReceived;
static PyObject *cls_ChunkDelivered;
static PyObject *cls_CancelConfirmed;
static PyObject *cls_BdpEstimated;
static PyObject *cls_TimerFired;
static PyObject *cls_TcpInfo;

/* Action types for isinstance checks */
static PyObject *cls_AssignChunk;
static PyObject *cls_CancelChunk;
static PyObject *cls_SetTimer;
static PyObject *cls_StartProbe;
static PyObject *cls_AbortProbe;

/* ---------------------------------------------------------------------------
 * Timer management: one timerfd per peer + one for rebalance.
 * peer_id → timerfd mapping.  peer_id == -1 is the rebalance timer.
 * We store fds in a simple array indexed by peer slot.
 * Slot MAX_PEERS is the rebalance timer.
 * ------------------------------------------------------------------------ */

#define REBALANCE_TIMER_SLOT MAX_PEERS
static int timer_fds[MAX_PEERS + 1];

/* Separate timerfds for the oracle "probe complete" delay, keyed by
 * peer node_id. Armed on StartProbe, fired after ORACLE_DELAY_RTTS ×
 * RTmin to simulate the latency a real estimator would incur before
 * finalizing a BDP value. Cancellable by AbortProbe (the race that
 * makes AbortProbe non-trivially interesting). */
#define ORACLE_DELAY_RTTS     3
#define ORACLE_DELAY_MIN_MS   20
static int  oracle_timer_fds[ORACLE_NODE_IDS];
static bool oracle_pending[ORACLE_NODE_IDS];

static void init_timer_fds(void) {
    for (int i = 0; i <= MAX_PEERS; i++)
        timer_fds[i] = -1;
    for (int i = 0; i < ORACLE_NODE_IDS; i++) {
        oracle_timer_fds[i] = -1;
        oracle_pending[i] = false;
    }
}

static int get_timer_slot(int peer_id) {
    if (peer_id < 0) return REBALANCE_TIMER_SLOT;
    /* Find peer's slot index */
    for (int i = 0; i < G.num_peers; i++) {
        /* Match by peer_id.  peer_id in the scheduler is the node_id
         * derived from the IP: 10.0.0.<node_id>. */
        int nid = ntohl(G.peers[i].addr_ip) & 0xFF;
        if (nid == peer_id) return i;
    }
    return -1;
}

static void arm_timer(int slot, int delay_ms) {
    if (slot < 0 || slot > MAX_PEERS) return;

    if (timer_fds[slot] < 0) {
        timer_fds[slot] = timerfd_create(CLOCK_MONOTONIC, TFD_NONBLOCK);
        if (timer_fds[slot] < 0) {
            logmsg("WARN: timerfd_create failed for scheduler timer");
            return;
        }
        /* Register with epoll.  Use a sentinel pointer offset to identify
         * scheduler timers in the event loop. */
        struct epoll_event ev;
        ev.events = EPOLLIN;
        /* Encode slot in the pointer: (void*)(intptr_t)(-100 - slot) */
        ev.data.ptr = (void *)(intptr_t)(-100 - slot);
        epoll_ctl(G.epoll_fd, EPOLL_CTL_ADD, timer_fds[slot], &ev);
    }

    struct itimerspec its;
    memset(&its, 0, sizeof(its));
    its.it_value.tv_sec = delay_ms / 1000;
    its.it_value.tv_nsec = (delay_ms % 1000) * 1000000L;
    if (its.it_value.tv_sec == 0 && its.it_value.tv_nsec == 0)
        its.it_value.tv_nsec = 1000000;  /* minimum 1ms */
    timerfd_settime(timer_fds[slot], 0, &its, NULL);
}

static void arm_oracle_timer(int peer_id, int delay_ms) {
    if (peer_id < 0 || peer_id >= ORACLE_NODE_IDS) return;
    if (oracle_timer_fds[peer_id] < 0) {
        oracle_timer_fds[peer_id] = timerfd_create(CLOCK_MONOTONIC, TFD_NONBLOCK);
        if (oracle_timer_fds[peer_id] < 0) {
            logmsg("WARN: timerfd_create failed for oracle timer");
            return;
        }
        struct epoll_event ev;
        ev.events = EPOLLIN;
        /* Encode peer_id in the pointer: (-10000 - peer_id). Separate
         * range from stall/rebalance timers (-100 - slot). */
        ev.data.ptr = (void *)(intptr_t)(-10000 - peer_id);
        epoll_ctl(G.epoll_fd, EPOLL_CTL_ADD, oracle_timer_fds[peer_id], &ev);
    }
    struct itimerspec its;
    memset(&its, 0, sizeof(its));
    its.it_value.tv_sec  = delay_ms / 1000;
    its.it_value.tv_nsec = (delay_ms % 1000) * 1000000L;
    if (its.it_value.tv_sec == 0 && its.it_value.tv_nsec == 0)
        its.it_value.tv_nsec = 1000000;
    timerfd_settime(oracle_timer_fds[peer_id], 0, &its, NULL);
}

static void disarm_oracle_timer(int peer_id) {
    if (peer_id < 0 || peer_id >= ORACLE_NODE_IDS) return;
    if (oracle_timer_fds[peer_id] < 0) return;
    /* Drain any pending expiration notification, disarm future fires. */
    struct itimerspec its = { {0,0}, {0,0} };
    timerfd_settime(oracle_timer_fds[peer_id], 0, &its, NULL);
    uint64_t expirations;
    read(oracle_timer_fds[peer_id], &expirations, sizeof(expirations));
}

/* ---------------------------------------------------------------------------
 * TCP_INFO helper
 * ------------------------------------------------------------------------ */

/* Build a TcpInfo for the Python scheduler. RTT comes from tcpi_rtt (real,
 * observable on our side). BDP comes from the burst-probe estimator — see
 * DESIGN.md "BDP estimation". We feed tcpi_rtt into the estimator here so
 * it can maintain its RTmin filter during Probing.
 *
 * tcpi_snd_cwnd is NOT used: on a download socket it reports our own send
 * cwnd (pinned at ~10 MSS because we only emit tiny MSG_REQUESTs), not the
 * peer's send cwnd. */
static PyObject *build_tcp_info(peer_t *p) {
    struct tcp_info ti;
    socklen_t len = sizeof(ti);
    memset(&ti, 0, sizeof(ti));
    if (p->connected)
        getsockopt(p->fd, IPPROTO_TCP, TCP_INFO, &ti, &len);

    /* BDP is not carried in TcpInfo — it flows to Python via explicit
     * BdpEstimated events (fired from the oracle stub on StartProbe).
     * TcpInfo is RTT-only. */
    return PyObject_CallFunction(cls_TcpInfo, "i", (int)ti.tcpi_rtt);
}

static PyObject *build_all_tcp_infos(void) {
    PyObject *d = PyDict_New();
    for (int i = 0; i < G.num_peers; i++) {
        peer_t *p = &G.peers[i];
        if (!p->connected) continue;
        int nid = ntohl(p->addr_ip) & 0xFF;
        PyObject *key = PyLong_FromLong(nid);
        PyObject *val = build_tcp_info(p);
        PyDict_SetItem(d, key, val);
        Py_DECREF(key);
        Py_DECREF(val);
    }
    return d;
}

/* ---------------------------------------------------------------------------
 * Action execution
 * ------------------------------------------------------------------------ */

/* Forward declarations for protocol functions in diffusion.c */
void send_request_bitmap(peer_t *p, const uint8_t hash[HASH_SIZE],
                         int seqno,
                         const uint8_t *bitmap, size_t bitmap_len);
void send_cancel_chunk(peer_t *p, int seqno);

static peer_t *find_peer_by_id(int peer_id) {
    for (int i = 0; i < G.num_peers; i++) {
        int nid = ntohl(G.peers[i].addr_ip) & 0xFF;
        if (nid == peer_id) return &G.peers[i];
    }
    return NULL;
}

static void execute_actions(PyObject *actions) {
    Py_ssize_t n = PyList_Size(actions);
    for (Py_ssize_t i = 0; i < n; i++) {
        PyObject *action = PyList_GetItem(actions, i);

        if (PyObject_IsInstance(action, cls_AssignChunk)) {
            int peer_id = PyLong_AsLong(PyObject_GetAttrString(action, "peer_id"));
            PyObject *py_hash = PyObject_GetAttrString(action, "payload_hash");
            int seqno = PyLong_AsLong(PyObject_GetAttrString(action, "seqno"));
            PyObject *py_bitmap = PyObject_GetAttrString(action, "component_bitmap");

            const uint8_t *hash = (const uint8_t *)PyBytes_AsString(py_hash);
            const uint8_t *bitmap = (const uint8_t *)PyBytes_AsString(py_bitmap);
            Py_ssize_t bitmap_len = PyBytes_Size(py_bitmap);

            peer_t *p = find_peer_by_id(peer_id);
            if (p) {
                send_request_bitmap(p, hash, seqno, bitmap, bitmap_len);
            }

            Py_DECREF(py_hash);
            Py_DECREF(py_bitmap);

        } else if (PyObject_IsInstance(action, cls_CancelChunk)) {
            int peer_id = PyLong_AsLong(PyObject_GetAttrString(action, "peer_id"));
            int seqno = PyLong_AsLong(PyObject_GetAttrString(action, "seqno"));

            peer_t *p = find_peer_by_id(peer_id);
            if (p) {
                send_cancel_chunk(p, seqno);
            }

        } else if (PyObject_IsInstance(action, cls_SetTimer)) {
            PyObject *py_peer_id = PyObject_GetAttrString(action, "peer_id");
            int delay_ms = PyLong_AsLong(PyObject_GetAttrString(action, "delay_ms"));

            int peer_id = (py_peer_id == Py_None) ? -1 : PyLong_AsLong(py_peer_id);
            int slot = get_timer_slot(peer_id);
            if (slot >= 0)
                arm_timer(slot, delay_ms);

            Py_DECREF(py_peer_id);

        } else if (PyObject_IsInstance(action, cls_StartProbe)) {
            /* Oracle stub with realistic delay: arm a timerfd that
             * will fire BdpEstimated after several RTTs. The delay
             * makes the AbortProbe race meaningful — Python may snub
             * the peer before the oracle fires. */
            int peer_id = PyLong_AsLong(PyObject_GetAttrString(action, "peer_id"));
            if (peer_id >= 0 && peer_id < ORACLE_NODE_IDS) {
                int rtt_us = G.oracle_rtmin_us[peer_id];
                int delay_ms = (rtt_us > 0) ? (rtt_us * ORACLE_DELAY_RTTS / 1000)
                                            : ORACLE_DELAY_MIN_MS;
                if (delay_ms < ORACLE_DELAY_MIN_MS) delay_ms = ORACLE_DELAY_MIN_MS;
                oracle_pending[peer_id] = true;
                arm_oracle_timer(peer_id, delay_ms);
            }

        } else if (PyObject_IsInstance(action, cls_AbortProbe)) {
            int peer_id = PyLong_AsLong(PyObject_GetAttrString(action, "peer_id"));
            if (peer_id >= 0 && peer_id < ORACLE_NODE_IDS) {
                oracle_pending[peer_id] = false;
                disarm_oracle_timer(peer_id);
            }
        }
    }
}

/* ---------------------------------------------------------------------------
 * Call step() with an event
 * ------------------------------------------------------------------------ */

static void call_step(PyObject *event) {
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    PyObject *actions = PyObject_CallFunction(py_step_fn, "OO", py_state, event);
    if (!actions) {
        PyErr_Print();
        return;
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double step_us = (t1.tv_sec - t0.tv_sec) * 1e6 + (t1.tv_nsec - t0.tv_nsec) / 1e3;
    logmsg("SCHED step=%.0fus actions=%zd", step_us, PyList_Size(actions));
    /* Instrumentation for the "Python blocks the epoll loop" hypothesis:
     * flag any step that took longer than 1 ms — during which no sockets
     * were being read. Grep for SLOWSTEP to find candidates. */
    if (step_us >= 1000.0)
        logmsg("SLOWSTEP step=%.0fus", step_us);

    execute_actions(actions);
    Py_DECREF(actions);
    Py_DECREF(event);
}

/* ---------------------------------------------------------------------------
 * Public API: init
 * ------------------------------------------------------------------------ */

void scheduler_init(int hedge_threshold_bytes) {
    init_timer_fds();

    Py_Initialize();

    /* Add the working directory to sys.path so FetchScheduler can be imported. */
    PyObject *sys_path = PySys_GetObject("path");
    PyObject *cwd = PyUnicode_FromString("/sim");
    PyList_Append(sys_path, cwd);
    Py_DECREF(cwd);

    const char *module_name = getenv("SCHEDULER_MODULE");
    if (!module_name || !*module_name) module_name = "FetchScheduler";
    py_module = PyImport_ImportModule(module_name);
    if (!py_module) {
        PyErr_Print();
        logmsg("ERROR: failed to import %s", module_name);
        return;
    }
    logmsg("scheduler module: %s", module_name);

    /* Cache class references */
    cls_ManifestReceived = PyObject_GetAttrString(py_module, "ManifestReceived");
    cls_OfferReceived = PyObject_GetAttrString(py_module, "OfferReceived");
    cls_ChunkDelivered = PyObject_GetAttrString(py_module, "ChunkDelivered");
    cls_CancelConfirmed = PyObject_GetAttrString(py_module, "CancelConfirmed");
    cls_BdpEstimated = PyObject_GetAttrString(py_module, "BdpEstimated");
    cls_TimerFired = PyObject_GetAttrString(py_module, "TimerFired");
    cls_TcpInfo = PyObject_GetAttrString(py_module, "TcpInfo");
    cls_AssignChunk = PyObject_GetAttrString(py_module, "AssignChunk");
    cls_CancelChunk = PyObject_GetAttrString(py_module, "CancelChunk");
    cls_SetTimer = PyObject_GetAttrString(py_module, "SetTimer");
    cls_StartProbe = PyObject_GetAttrString(py_module, "StartProbe");
    cls_AbortProbe = PyObject_GetAttrString(py_module, "AbortProbe");

    py_step_fn = PyObject_GetAttrString(py_module, "step");

    /* Create initial state */
    PyObject *init_fn = PyObject_GetAttrString(py_module, "init_state");
    py_state = PyObject_CallFunction(init_fn, "i", hedge_threshold_bytes);
    Py_DECREF(init_fn);

    if (!py_state) {
        PyErr_Print();
        logmsg("ERROR: failed to create scheduler state");
    }

    logmsg("scheduler initialized (hedge_threshold=%d)", hedge_threshold_bytes);
}

/* ---------------------------------------------------------------------------
 * Elapsed time helper
 * ------------------------------------------------------------------------ */

static double elapsed(void) {
    struct timespec now;
    clock_gettime(CLOCK_REALTIME, &now);
    return (now.tv_sec + now.tv_nsec / 1e9) - G.start_time;
}

/* ---------------------------------------------------------------------------
 * Public API: events
 * ------------------------------------------------------------------------ */

void scheduler_peer_hint(int peer_id, int bw_mbit, int rtt_us) {
    /* Stash topology-derived oracle values for the BDP stub. These are
     * consumed by the StartProbe action handler until we have a real
     * receiver-side BDP estimator (see bdp_demo/). The RTT the scheduler
     * itself uses comes from live tcpi_rtt, not from here. */
    if (peer_id >= 0 && peer_id < ORACLE_NODE_IDS) {
        uint64_t bdp = (uint64_t)bw_mbit * 1000000ULL / 8ULL
                       * (uint64_t)rtt_us / 1000000ULL;
        G.oracle_bdp_bytes[peer_id] = bdp;
        G.oracle_rtmin_us[peer_id]  = rtt_us;
    }

    PyObject *py_tcp_info = PyObject_CallFunction(cls_TcpInfo, "i", rtt_us);

    PyObject *event = PyObject_CallFunction(
        PyObject_GetAttrString(py_module, "PeerHint"), "iOd",
        peer_id, py_tcp_info, elapsed());
    Py_DECREF(py_tcp_info);

    call_step(event);
}

void scheduler_manifest_received(const uint8_t hash[HASH_SIZE],
                                 const uint16_t *comp_sizes,
                                 uint16_t num_components) {
    PyObject *py_hash = PyBytes_FromStringAndSize((const char *)hash, HASH_SIZE);
    PyObject *py_sizes = PyTuple_New(num_components);
    for (int i = 0; i < num_components; i++)
        PyTuple_SetItem(py_sizes, i, PyLong_FromLong(comp_sizes[i]));

    PyObject *event = PyObject_CallFunction(cls_ManifestReceived, "OOd",
        py_hash, py_sizes, elapsed());
    Py_DECREF(py_hash);
    Py_DECREF(py_sizes);

    call_step(event);
}

void scheduler_offer_received(int peer_id,
                              const uint8_t hash[HASH_SIZE],
                              peer_t *peer) {
    PyObject *py_hash = PyBytes_FromStringAndSize((const char *)hash, HASH_SIZE);
    PyObject *py_tcp_info = build_tcp_info(peer);

    PyObject *event = PyObject_CallFunction(cls_OfferReceived, "iOOd",
        peer_id, py_hash, py_tcp_info, elapsed());
    Py_DECREF(py_hash);
    Py_DECREF(py_tcp_info);

    call_step(event);
}

void scheduler_chunk_delivered(int peer_id,
                               int seqno,
                               peer_t *peer) {
    PyObject *py_tcp_info = build_tcp_info(peer);

    PyObject *event = PyObject_CallFunction(cls_ChunkDelivered, "iiOd",
        peer_id, seqno, py_tcp_info, elapsed());
    Py_DECREF(py_tcp_info);

    call_step(event);
}

void scheduler_cancel_confirmed(int peer_id,
                                int seqno,
                                peer_t *peer) {
    PyObject *py_tcp_info = build_tcp_info(peer);

    PyObject *event = PyObject_CallFunction(cls_CancelConfirmed, "iiOd",
        peer_id, seqno, py_tcp_info, elapsed());
    Py_DECREF(py_tcp_info);

    call_step(event);
}

void scheduler_bdp_estimated(int peer_id, peer_t *peer) {
    /* Oracle stub: regurgitate the BDP and RTmin parsed from the
     * topology JSON at startup. A real receiver-side BDP estimator
     * would replace this with something measured from the socket;
     * see bdp_demo/ for why that's a non-trivial project. */
    (void)peer;
    int bdp_bytes = 0, rtmin_us = 0;
    if (peer_id >= 0 && peer_id < ORACLE_NODE_IDS) {
        bdp_bytes = (int)G.oracle_bdp_bytes[peer_id];
        rtmin_us  = G.oracle_rtmin_us[peer_id];
    }

    PyObject *event = PyObject_CallFunction(cls_BdpEstimated, "iiid",
        peer_id, bdp_bytes, rtmin_us, elapsed());

    call_step(event);
}

void scheduler_timer_fired(int peer_id) {
    PyObject *py_peer_id = (peer_id < 0) ? Py_None : PyLong_FromLong(peer_id);
    if (peer_id < 0) Py_INCREF(Py_None);

    PyObject *py_tcp_infos = build_all_tcp_infos();

    PyObject *event = PyObject_CallFunction(cls_TimerFired, "OOd",
        py_peer_id, py_tcp_infos, elapsed());
    Py_DECREF(py_peer_id);
    Py_DECREF(py_tcp_infos);

    call_step(event);
}

/* ---------------------------------------------------------------------------
 * Epoll integration: called from node.c's event loop
 * ------------------------------------------------------------------------ */

bool is_scheduler_timer(void *ptr) {
    intptr_t val = (intptr_t)ptr;
    return val <= -100 && val >= -100 - MAX_PEERS;
}

void handle_scheduler_timer(void *ptr) {
    intptr_t val = (intptr_t)ptr;
    int slot = (int)(-100 - val);

    /* Drain the timerfd */
    uint64_t expirations;
    read(timer_fds[slot], &expirations, sizeof(expirations));

    if (slot == REBALANCE_TIMER_SLOT) {
        scheduler_timer_fired(-1);
    } else {
        int nid = ntohl(G.peers[slot].addr_ip) & 0xFF;
        scheduler_timer_fired(nid);
    }
}

bool is_oracle_timer(void *ptr) {
    intptr_t val = (intptr_t)ptr;
    return val <= -10000 && val >= -10000 - ORACLE_NODE_IDS;
}

void handle_oracle_timer(void *ptr) {
    intptr_t val = (intptr_t)ptr;
    int peer_id = (int)(-10000 - val);

    uint64_t expirations;
    read(oracle_timer_fds[peer_id], &expirations, sizeof(expirations));

    /* AbortProbe may have raced us — if the probe was cancelled,
     * don't fire BdpEstimated. */
    if (!oracle_pending[peer_id]) return;
    oracle_pending[peer_id] = false;

    peer_t *p = find_peer_by_id(peer_id);
    if (p) scheduler_bdp_estimated(peer_id, p);
}
