/*
 * node.c — Infrastructure: networking, epoll event loop, schedule loading.
 *
 * Protocol logic lives in diffusion.c.
 *
 * Usage: ./node --id <N> --inputfile <file> --epoch <realtime>
 */

#include "node.h"
#include "scheduler_bridge.h"
#include "cJSON.h"
#include <signal.h>

/* ---------------------------------------------------------------------------
 * Global state definition
 * ------------------------------------------------------------------------ */

struct node_state G;

/* ---------------------------------------------------------------------------
 * Logging
 * ------------------------------------------------------------------------ */

void logmsg(const char *fmt, ...) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    double elapsed = (ts.tv_sec + ts.tv_nsec / 1e9) - G.start_time;
    fprintf(stderr, "[%s %.3f] ", G.node_name, elapsed);
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fprintf(stderr, "\n");
}

/* ---------------------------------------------------------------------------
 * Utility
 * ------------------------------------------------------------------------ */

int set_nonblocking(int fd) {
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags == -1) return -1;
    return fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}

/* ---------------------------------------------------------------------------
 * Write queue management
 * ------------------------------------------------------------------------ */

static void ensure_epollout(peer_t *p) {
    struct epoll_event ev;
    ev.events = EPOLLIN | EPOLLOUT;
    ev.data.ptr = p;
    epoll_ctl(G.epoll_fd, EPOLL_CTL_MOD, p->fd, &ev);
}

static void queue_append(write_buf_t **head, write_buf_t **tail,
                         const uint8_t *data, size_t len,
                         const uint8_t *payload_hash, uint32_t seqno) {
    write_buf_t *wb = malloc(sizeof(write_buf_t));
    wb->data = malloc(len);
    memcpy(wb->data, data, len);
    wb->len = len;
    wb->off = 0;
    wb->next = NULL;
    wb->payload_hash = payload_hash;
    wb->seqno = seqno;
    if (*tail) {
        (*tail)->next = wb;
    } else {
        *head = wb;
    }
    *tail = wb;
}

void peer_queue_write(peer_t *p, const uint8_t *data, size_t len) {
    queue_append(&p->wq_lo_head, &p->wq_lo_tail, data, len, NULL, UINT32_MAX);
    ensure_epollout(p);
}

void peer_queue_write_tagged(peer_t *p, const uint8_t *data, size_t len,
                             const uint8_t *payload_hash, uint32_t seqno) {
    queue_append(&p->wq_lo_head, &p->wq_lo_tail, data, len, payload_hash, seqno);
    ensure_epollout(p);
}

void peer_queue_write_priority(peer_t *p, const uint8_t *data, size_t len) {
    queue_append(&p->wq_hi_head, &p->wq_hi_tail, data, len, NULL, UINT32_MAX);
    ensure_epollout(p);
}

bool peer_purge_seqno(peer_t *p, uint32_t seqno) {
    /* Tagged entries are appended in ascending-seqno order (per-peer seqnos
     * are monotonic and we process REQUESTs sequentially), so once we pass
     * the target seqno we can stop. Skip if partially written.
     * Walk with (prev, wb) so unlink and tail fixup are O(1). */
    write_buf_t *prev = NULL;
    for (write_buf_t *wb = p->wq_lo_head; wb; prev = wb, wb = wb->next) {
        if (!wb->payload_hash) continue;
        if (wb->seqno > seqno) break;
        if (wb->seqno == seqno) {
            if (wb->off != 0) break;
            if (prev) prev->next = wb->next;
            else      p->wq_lo_head = wb->next;
            if (p->wq_lo_tail == wb) p->wq_lo_tail = prev;
            free(wb->data);
            free(wb);
            return true;
        }
    }
    return false;
}

/* Socket write trace: record (wallclock, dst_ip, dst_port, bytes_written)
 * to stdout.  18 bytes per record, packed. */
typedef struct __attribute__((packed)) {
    double   wallclock;
    uint32_t dst_ip;
    uint16_t dst_port;
    uint32_t bytes_written;
} write_trace_t;

static void trace_write_ts(peer_t *p, const struct timespec *ts,
                           uint32_t nbytes) {
    write_trace_t rec = {
        .wallclock = ts->tv_sec + ts->tv_nsec / 1e9,
        .dst_ip = p->addr_ip,
        .dst_port = p->addr_port,
        .bytes_written = nbytes,
    };
    write(STDOUT_FILENO, &rec, sizeof(rec));
}

/* Flush from a single queue until EAGAIN or the queue empties. Yields
 * early if the kernel's not-yet-sent backlog reaches NOTSENT_LOWAT —
 * write() itself ignores TCP_NOTSENT_LOWAT (only epoll respects it),
 * so we enforce the cap ourselves via SIOCOUTQNSD. Keeping notsent
 * below this cap minimises the window in which a late-arriving
 * MSG_CANCEL_CHUNK is "too late" to purge.
 * Returns true if the socket can still accept more data. */
static bool flush_queue(peer_t *p, write_buf_t **head, write_buf_t **tail) {
    while (*head) {
        write_buf_t *wb = *head;
        while (wb->off < wb->len) {
            struct timespec ts;
            clock_gettime(CLOCK_REALTIME, &ts);
            ssize_t n = write(p->fd, wb->data + wb->off, wb->len - wb->off);
            if (n <= 0) {
                if (n == 0 || errno == EAGAIN || errno == EWOULDBLOCK) return false;
                logmsg("write error to %s: %s", p->addr_str, strerror(errno));
                return false;
            }
            trace_write_ts(p, &ts, (uint32_t)n);
            wb->off += n;
            int notsent = 0;
            if (ioctl(p->fd, SIOCOUTQNSD, &notsent) == 0 && notsent >= NOTSENT_LOWAT)
                return false;
        }
        *head = wb->next;
        if (!*head) *tail = NULL;
        free(wb->data);
        free(wb);
    }
    return true;
}

/* If the head buffer is partially written, finish it.
 * Returns false if the socket blocked before completing. */
static bool flush_head_if_partial(peer_t *p, write_buf_t **head, write_buf_t **tail) {
    if (!*head || (*head)->off == 0) return true;
    write_buf_t *wb = *head;
    while (wb->off < wb->len) {
        ssize_t n = write(p->fd, wb->data + wb->off, wb->len - wb->off);
        if (n <= 0) {
            if (n == 0 || errno == EAGAIN || errno == EWOULDBLOCK) return false;
            logmsg("write error to %s: %s", p->addr_str, strerror(errno));
            return false;
        }
        wb->off += n;
    }
    *head = wb->next;
    if (!*head) *tail = NULL;
    free(wb->data);
    free(wb);
    return true;
}

static void peer_flush_writes(peer_t *p) {
    /* Finish any partially-written lo buffer before touching hi,
     * otherwise we'd interleave hi bytes into a lo message on the wire. */
    if (flush_head_if_partial(p, &p->wq_lo_head, &p->wq_lo_tail)
        && flush_queue(p, &p->wq_hi_head, &p->wq_hi_tail))
        flush_queue(p, &p->wq_lo_head, &p->wq_lo_tail);

    if (!p->wq_hi_head && !p->wq_lo_head) {
        struct epoll_event ev;
        ev.events = EPOLLIN;
        ev.data.ptr = p;
        epoll_ctl(G.epoll_fd, EPOLL_CTL_MOD, p->fd, &ev);
    }
}

/* ---------------------------------------------------------------------------
 * Network: accept incoming connection
 * ------------------------------------------------------------------------ */

/* Set by parse_use_bbr() at startup from the USE_BBR env var. */
static bool g_use_bbr = false;

static void parse_use_bbr(void) {
    const char *v = getenv("USE_BBR");
    if (v == NULL || strcmp(v, "0") == 0) {
        g_use_bbr = false;
    } else if (strcmp(v, "1") == 0) {
        g_use_bbr = true;
    } else {
        fprintf(stderr, "USE_BBR must be 0 or 1 (or unset); got '%s'\n", v);
        exit(1);
    }
}

/* Apply nonblocking + TCP tuning socket options common to accepted and
 * initiated sockets. rcvbuf is intentionally left to TCP auto-tune:
 * setsockopt(SO_RCVBUF) disables auto-tune and gets clamped to the
 * un-writable net.core.rmem_max inside a Mininet host netns. */
static void configure_socket(int fd) {
    set_nonblocking(fd);
    int one = 1;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
    int lowat = NOTSENT_LOWAT;
    if (setsockopt(fd, IPPROTO_TCP, TCP_NOTSENT_LOWAT, &lowat, sizeof(lowat)) < 0)
        logmsg("WARN: TCP_NOTSENT_LOWAT failed: %s", strerror(errno));
    if (g_use_bbr) {
        const char *cc = "bbr";
        if (setsockopt(fd, IPPROTO_TCP, TCP_CONGESTION, cc, strlen(cc)) < 0) {
            fprintf(stderr, "TCP_CONGESTION=bbr failed: %s\n", strerror(errno));
            exit(1);
        }
    }
}

/* Allocate a peer slot, populate its fields, register with epoll, and
 * kick off initial offer requests unless downstream-only. Caller must
 * have already configured `fd`. Returns NULL if MAX_PEERS is exceeded. */
static peer_t *register_peer(int fd, const char *addr_str,
                             uint32_t addr_ip, uint16_t addr_port,
                             bool downstream_only, bool is_listener,
                             uint32_t epoll_events) {
    if (G.num_peers >= MAX_PEERS) {
        logmsg("too many peers");
        return NULL;
    }
    peer_t *p = &G.peers[G.num_peers++];
    memset(p, 0, sizeof(*p));
    p->fd = fd;
    p->connected = true;
    p->is_listener = is_listener;
    p->downstream_only = downstream_only;
    snprintf(p->addr_str, sizeof(p->addr_str), "%s", addr_str);
    p->addr_ip = addr_ip;
    p->addr_port = addr_port;

    struct epoll_event ev;
    ev.events = epoll_events;
    ev.data.ptr = p;
    epoll_ctl(G.epoll_fd, EPOLL_CTL_ADD, fd, &ev);

    if (!p->downstream_only) {
        for (int i = 0; i < OFFER_WINDOW_INIT; i++)
            send_request_offer(p);
    }
    return p;
}

static void accept_connection(void) {
    struct sockaddr_in addr;
    socklen_t addrlen = sizeof(addr);
    int fd = accept(G.listen_fd, (struct sockaddr *)&addr, &addrlen);
    if (fd < 0) {
        if (errno != EAGAIN && errno != EWOULDBLOCK) {
            logmsg("accept error: %s", strerror(errno));
        }
        return;
    }

    configure_socket(fd);

    char addr_str[64];
    snprintf(addr_str, sizeof(addr_str), "%s:%d",
             inet_ntoa(addr.sin_addr), ntohs(addr.sin_port));

    int peer_node_id = ntohl(addr.sin_addr.s_addr) & 0xFF;
    bool downstream_only = (G.downstream_only_peers >> peer_node_id) & 1;

    peer_t *p = register_peer(fd, addr_str,
                              addr.sin_addr.s_addr, addr.sin_port,
                              downstream_only, /*is_listener=*/true,
                              EPOLLIN);
    if (!p) {
        close(fd);
        logmsg("too many peers, rejecting connection from %s", addr_str);
        return;
    }
    logmsg("accepted connection from %s", p->addr_str);
}

/* ---------------------------------------------------------------------------
 * Network: initiate outgoing connection to peer
 * ------------------------------------------------------------------------ */

static peer_t *connect_to_peer(const char *addr_str, bool downstream_only) {
    char host[64];
    int port;
    if (sscanf(addr_str, "%63[^:]:%d", host, &port) != 2) {
        logmsg("bad peer address: %s", addr_str);
        return NULL;
    }

    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) {
        logmsg("socket: %s", strerror(errno));
        return NULL;
    }

    configure_socket(fd);

    struct sockaddr_in sa;
    memset(&sa, 0, sizeof(sa));
    sa.sin_family = AF_INET;
    sa.sin_port = htons(port);
    inet_pton(AF_INET, host, &sa.sin_addr);

    int ret = connect(fd, (struct sockaddr *)&sa, sizeof(sa));
    if (ret < 0 && errno != EINPROGRESS) {
        logmsg("connect to %s: %s", addr_str, strerror(errno));
        close(fd);
        return NULL;
    }

    /* EPOLLOUT lets us detect connect completion. */
    peer_t *p = register_peer(fd, addr_str,
                              sa.sin_addr.s_addr, sa.sin_port,
                              downstream_only, /*is_listener=*/false,
                              EPOLLIN | EPOLLOUT);
    if (!p) {
        close(fd);
        return NULL;
    }
    logmsg("connecting to %s", addr_str);
    return p;
}

/* ---------------------------------------------------------------------------
 * Network: process incoming data for a peer
 * ------------------------------------------------------------------------ */

static void peer_on_readable(peer_t *p) {
    ssize_t n = read(p->fd, p->rbuf + p->rbuf_len,
                     READ_BUF_SIZE - p->rbuf_len);
    if (n <= 0) {
        if (n == 0) {
            logmsg("peer %s disconnected", p->addr_str);
        } else if (errno != EAGAIN && errno != EWOULDBLOCK) {
            logmsg("read error from %s: %s", p->addr_str, strerror(errno));
        }
        if (n == 0) {
            epoll_ctl(G.epoll_fd, EPOLL_CTL_DEL, p->fd, NULL);
            close(p->fd);
            p->connected = false;
        }
        return;
    }
    p->rbuf_len += n;
    p->bytes_read += n;

    /* Instrumentation for the "Python blocks the epoll loop" hypothesis:
     * a single read() returning a large batch means the kernel had been
     * accumulating data while we were elsewhere. Grep for BIGREAD. */
    if ((size_t)n >= 64 * 1024)
        logmsg("BIGREAD peer=%s n=%zd", p->addr_str, (ssize_t)n);

    /* No receiver-side BDP sampling here: the estimator is currently
     * an oracular stub fed at StartProbe time; see bdp_estimator.h
     * and bdp_demo/ for why. */

    size_t off = 0;
    while (off < p->rbuf_len) {
        size_t consumed = handle_message(p, p->rbuf + off, p->rbuf_len - off);
        if (consumed == 0) break;
        off += consumed;
    }

    if (off > 0) {
        p->rbuf_len -= off;
        if (p->rbuf_len > 0) {
            memmove(p->rbuf, p->rbuf + off, p->rbuf_len);
        }
    }

    /* No async BDP estimator transition to poll for: the oracle stub
     * fires BdpEstimated synchronously from the StartProbe action
     * handler. This hook can come back when a real estimator replaces
     * the stub. */
}

/* ---------------------------------------------------------------------------
 * Schedule: loading and timer
 * ------------------------------------------------------------------------ */

static void arm_schedule_timer(void);

static int schedule_cmp(const void *a, const void *b) {
    double ta = ((const schedule_entry_t *)a)->time;
    double tb = ((const schedule_entry_t *)b)->time;
    return (ta > tb) - (ta < tb);
}

static void load_schedule(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) {
        logmsg("ERROR: cannot open schedule file: %s", path);
        return;
    }

    fseek(f, 0, SEEK_END);
    long fsize = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = malloc(fsize + 1);
    fread(buf, 1, fsize, f);
    buf[fsize] = '\0';
    fclose(f);

    cJSON *root = cJSON_Parse(buf);
    free(buf);
    if (!root || !cJSON_IsObject(root)) {
        logmsg("ERROR: input file is not a JSON object");
        cJSON_Delete(root);
        return;
    }
    cJSON *schedule = cJSON_GetObjectItem(root, "schedule");
    if (!schedule || !cJSON_IsArray(schedule)) {
        logmsg("ERROR: input file has no 'schedule' array");
        cJSON_Delete(root);
        return;
    }

    cJSON *entry;
    cJSON_ArrayForEach(entry, schedule) {
        cJSON *j_time = cJSON_GetObjectItem(entry, "time");
        cJSON *j_node = cJSON_GetObjectItem(entry, "node");
        cJSON *j_nick = cJSON_GetObjectItem(entry, "nickname");
        cJSON *j_comp = cJSON_GetObjectItem(entry, "components");

        if (!j_time || !j_node ||
            !j_nick || !cJSON_IsString(j_nick) ||
            !j_comp || !cJSON_IsArray(j_comp)) {
            logmsg("ERROR: schedule entry needs time, node, nickname, components");
            exit(1);
        }

        /* time and node must agree in shape: either both scalars (a
         * single injection) or both arrays of equal, non-zero length
         * (the same payload magically injected at several (time, node)
         * pairs). */
        bool time_arr = cJSON_IsArray(j_time);
        bool node_arr = cJSON_IsArray(j_node);
        if (time_arr != node_arr) {
            logmsg("ERROR: schedule entry time/node must both be scalars or both arrays");
            exit(1);
        }
        int n_inj = time_arr ? cJSON_GetArraySize(j_time) : 1;
        if (time_arr && cJSON_GetArraySize(j_node) != n_inj) {
            logmsg("ERROR: schedule entry time/node arrays have different lengths");
            exit(1);
        }
        if (n_inj == 0) {
            logmsg("ERROR: schedule entry time/node arrays must be non-empty");
            exit(1);
        }

        for (int i = 0; i < n_inj; i++) {
            cJSON *j_t = time_arr ? cJSON_GetArrayItem(j_time, i) : j_time;
            cJSON *j_n = node_arr ? cJSON_GetArrayItem(j_node, i) : j_node;
            if (j_n->valueint != G.node_id) continue;

            if (G.schedule_count >= MAX_PAYLOADS) {
                logmsg("WARN: schedule table full, ignoring remaining entries");
                break;
            }

            schedule_entry_t *se = &G.schedule[G.schedule_count];
            memset(se, 0, sizeof(*se));
            se->time = j_t->valuedouble;
            snprintf(se->nickname, sizeof(se->nickname), "%s", j_nick->valuestring);

            cJSON *comp;
            cJSON_ArrayForEach(comp, j_comp) {
                if (se->num_components >= MAX_COMPONENTS) break;
                se->comp_sizes[se->num_components++] = (uint16_t)comp->valueint;
            }

            G.schedule_count++;
        }
    }

    cJSON_Delete(root);

    qsort(G.schedule, G.schedule_count, sizeof(schedule_entry_t), schedule_cmp);
    logmsg("loaded %d schedule entries for node %d", G.schedule_count, G.node_id);
}

static void arm_schedule_timer(void) {
    if (G.schedule_next >= G.schedule_count) {
        struct itimerspec its = { {0, 0}, {0, 0} };
        timerfd_settime(G.timer_fd, 0, &its, NULL);
        return;
    }

    /* Schedule times are relative to process start */
    double target = G.start_time + G.schedule[G.schedule_next].time;

    struct timespec now;
    clock_gettime(CLOCK_REALTIME, &now);
    double now_sec = now.tv_sec + now.tv_nsec / 1e9;
    double delay = target - now_sec;
    if (delay < 0.000001) delay = 0.000001;  /* >0 so timerfd doesn't disarm */

    struct itimerspec its;
    memset(&its, 0, sizeof(its));
    its.it_value.tv_sec = (time_t)delay;
    its.it_value.tv_nsec = (long)((delay - (time_t)delay) * 1e9);

    timerfd_settime(G.timer_fd, 0, &its, NULL);
}

/* ---------------------------------------------------------------------------
 * SIGTERM handler: Shadow sends this at shutdown_time.
 * ------------------------------------------------------------------------ */

static void handle_sigterm(int sig) {
    (void)sig;
    fflush(stdout);
    fflush(stderr);
    _exit(0);
}



/* ---------------------------------------------------------------------------
 * Main
 * ------------------------------------------------------------------------ */

int main(int argc, char **argv) {
    if (argc < 7 || strcmp(argv[1], "--id") != 0
                  || strcmp(argv[3], "--inputfile") != 0
                  || strcmp(argv[5], "--epoch") != 0) {
        fprintf(stderr, "Usage: %s --id <N> --inputfile <file> --epoch <realtime>\n", argv[0]);
        return 1;
    }

    signal(SIGTERM, handle_sigterm);
    srand(time(NULL) ^ getpid());

    parse_use_bbr();

    G.start_time = strtod(argv[6], NULL);

    G.node_id = atoi(argv[2]);
    const char *inputfile_path = argv[4];
    G.listen_port = 9000 + G.node_id;

    snprintf(G.node_name, sizeof(G.node_name), "node:%d", G.node_id);

    logmsg("starting (port=%u) start_realtime=%.6f", G.listen_port, G.start_time);

    G.epoll_fd = epoll_create1(0);
    if (G.epoll_fd < 0) {
        perror("epoll_create1");
        return 1;
    }

    G.listen_fd = socket(AF_INET, SOCK_STREAM, 0);
    if (G.listen_fd < 0) {
        perror("socket");
        return 1;
    }

    int one = 1;
    setsockopt(G.listen_fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
    set_nonblocking(G.listen_fd);

    struct sockaddr_in sa;
    memset(&sa, 0, sizeof(sa));
    sa.sin_family = AF_INET;
    sa.sin_addr.s_addr = INADDR_ANY;
    sa.sin_port = htons(G.listen_port);

    if (bind(G.listen_fd, (struct sockaddr *)&sa, sizeof(sa)) < 0) {
        perror("bind");
        return 1;
    }

    if (listen(G.listen_fd, 16) < 0) {
        perror("listen");
        return 1;
    }

    struct epoll_event ev;
    ev.events = EPOLLIN;
    ev.data.ptr = NULL;  /* NULL = listen socket sentinel */
    epoll_ctl(G.epoll_fd, EPOLL_CTL_ADD, G.listen_fd, &ev);

    /* Initialize the fetch scheduler (embedded Python). */
    scheduler_init(256 * 1024);  /* hedge threshold: 256 KB */

    /* Parse edges from input.json and connect to peers with higher IDs. */
    {
        FILE *f = fopen(inputfile_path, "r");
        if (!f) { logmsg("ERROR: cannot open %s", inputfile_path); return 1; }
        fseek(f, 0, SEEK_END);
        long fsize = ftell(f);
        fseek(f, 0, SEEK_SET);
        char *buf = malloc(fsize + 1);
        fread(buf, 1, fsize, f);
        buf[fsize] = '\0';
        fclose(f);

        cJSON *root = cJSON_Parse(buf);
        free(buf);
        cJSON *edges = cJSON_GetObjectItem(root, "edges");
        cJSON *edge;
        cJSON_ArrayForEach(edge, edges) {
            int a = cJSON_GetObjectItem(edge, "a")->valueint;
            int b = cJSON_GetObjectItem(edge, "b")->valueint;
            bool a_pulls = cJSON_IsTrue(cJSON_GetObjectItem(edge, "a_pulls"));
            bool b_pulls = cJSON_IsTrue(cJSON_GetObjectItem(edge, "b_pulls"));

            /* Identify the other node and whether we initiate the connection. */
            int peer_id = -1;
            if (a == G.node_id) peer_id = b;
            else if (b == G.node_id) peer_id = a;
            else continue;  /* edge doesn't involve us */

            /* downstream_only: we never pull from this peer */
            bool downstream_only = (G.node_id == a) ? !a_pulls : !b_pulls;

            if (downstream_only)
                G.downstream_only_peers |= (1ULL << peer_id);

            /* Give the scheduler a synthetic TCP_INFO hint from the topology. */
            {
                int bw_mbit = cJSON_GetObjectItem(edge, "bw_mbit")->valueint;
                int delay_ms = atoi(cJSON_GetObjectItem(edge, "delay")->valuestring);
                int rtt_us = delay_ms * 2 * 1000;
                scheduler_peer_hint(peer_id, bw_mbit, rtt_us);
            }

            /* Lower ID initiates the TCP connection. */
            if (peer_id < G.node_id) continue;  /* they connect to us */

            char addr[32];
            snprintf(addr, sizeof(addr), "10.0.0.%d:%d", peer_id, 9000 + peer_id);
            connect_to_peer(addr, downstream_only);
        }
        cJSON_Delete(root);
    }

    G.timer_fd = timerfd_create(CLOCK_MONOTONIC, TFD_NONBLOCK);
    ev.events = EPOLLIN;
    ev.data.ptr = (void *)(intptr_t)-1;  /* -1 = timer sentinel */
    epoll_ctl(G.epoll_fd, EPOLL_CTL_ADD, G.timer_fd, &ev);

    load_schedule(inputfile_path);
    arm_schedule_timer();

    logmsg("listening on port %u, %d outgoing peers",
           G.listen_port, G.num_peers);


    struct epoll_event events[EPOLL_MAX_EVENTS];
    for (;;) {
        int nev = epoll_wait(G.epoll_fd, events, EPOLL_MAX_EVENTS, -1);
        if (nev < 0) {
            if (errno == EINTR) continue;
            perror("epoll_wait");
            break;
        }

        for (int i = 0; i < nev; i++) {
            void *ptr = events[i].data.ptr;

            if (ptr == NULL) {
                accept_connection();
            } else if (is_scheduler_timer(ptr)) {
                handle_scheduler_timer(ptr);
            } else if (is_oracle_timer(ptr)) {
                handle_oracle_timer(ptr);
            } else if (ptr == (void *)(intptr_t)-1) {
                uint64_t expirations;
                read(G.timer_fd, &expirations, sizeof(expirations));
                while (G.schedule_next < G.schedule_count) {
                    struct timespec now;
                    clock_gettime(CLOCK_REALTIME, &now);
                    double now_sec = now.tv_sec + now.tv_nsec / 1e9;
                    if (G.start_time + G.schedule[G.schedule_next].time > now_sec + 0.001)
                        break;
                    inject_scheduled_payload();
                    G.schedule_next++;
                }
                arm_schedule_timer();
            } else {
                peer_t *p = (peer_t *)ptr;
                if (events[i].events & (EPOLLIN | EPOLLHUP | EPOLLERR)) {
                    peer_on_readable(p);
                }
                if (events[i].events & EPOLLOUT) {
                    peer_flush_writes(p);
                }
            }
        }
    }

    return 0;
}
