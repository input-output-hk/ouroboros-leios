#ifndef NODE_H
#define NODE_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdarg.h>
#include <unistd.h>
#include <errno.h>
#include <time.h>
#include <sys/epoll.h>
#include <sys/socket.h>
#include <sys/timerfd.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <endian.h>
#include <sys/ioctl.h>
#include <linux/sockios.h>

/* ---------------------------------------------------------------------------
 * Constants
 * ------------------------------------------------------------------------ */

#define HASH_SIZE           32  /* SHA-256 */

#define MAX_PEERS           16
#define MAX_PAYLOADS        1024
#define MAX_COMPONENTS      15000
#define MAX_COMPONENT_SIZE  16384
#define MIN_COMPONENT_SIZE  30
#define MAX_PAYLOAD_SIZE    (12 * 1024 * 1024)  /* 12 MB */

/* Manifest: (32B hash + 2B size) per component */
#define MANIFEST_ENTRY_SIZE (HASH_SIZE + 2)

#define OFFER_WINDOW_INIT   300
#define OFFER_WINDOW_REFILL 100

#define EPOLL_MAX_EVENTS    64
#define READ_BUF_SIZE       (256 * 1024)
#define REQUEST_CHUNK_BYTES (64 * 1024)  /* max component data per REQUEST/RESPONSE pair */
#define NOTSENT_LOWAT       (512 * 1024)  /* keep kernel send buffer shallow */
/* ---------------------------------------------------------------------------
 * Data structures
 * ------------------------------------------------------------------------ */

/* A single component */
typedef struct {
    uint16_t size;
    uint8_t  data[MAX_COMPONENT_SIZE];
} component_t;

/* A payload, identified by the SHA-256 hash of its manifest.
 *
 * Lifecycle:
 *   1. Receive MSG_OFFER_MANIFEST → create entry with hash, manifest_size
 *   2. Receive MSG_RESPONSE_MANIFEST → parse manifest, allocate component arrays
 *   3. Receive MSG_OFFER → request missing components
 *   4. Receive MSG_RESPONSE → store component data
 *   5. All components received → complete
 */
typedef struct {
    uint8_t     manifest_hash[HASH_SIZE]; /* identifies both manifest and payload */

    /* Manifest (NULL manifest_data means we don't have it yet) */
    uint8_t    *manifest_data;      /* raw bytes: (32B hash + 2B size) per component */
    uint32_t    manifest_size;      /* byte length of manifest_data */

    /* Components (populated after manifest is parsed).
     * A component is present iff components[i].size > 0 (min is 30). */
    uint16_t    num_components;
    uint16_t   *comp_sizes;         /* heap-allocated, from manifest */
    uint8_t   (*comp_hashes)[HASH_SIZE]; /* heap-allocated, from manifest */
    component_t *components;        /* heap-allocated */
    uint16_t    num_have;
    bool        complete;           /* all components received */

    uint64_t    offered_by;         /* bitmask: which peers have offered this payload */
    uint64_t    requested_from;     /* bitmask: which peers we've sent requests to */

    struct timespec first_seen;
    struct timespec completed_at;
} payload_t;

/* Write buffer: outgoing data queued for a peer */
typedef struct write_buf {
    uint8_t *data;
    size_t   len;
    size_t   off;
    struct write_buf *next;
    const uint8_t *payload_hash;  /* points into payload_t; NULL for non-RESPONSE */
    uint32_t seqno;               /* meaningful only when payload_hash != NULL */
} write_buf_t;

/* Per-peer state */
typedef struct {
    int       fd;
    bool      connected;
    bool      is_listener;
    bool      downstream_only; /* if true, we never pull from this peer */

    /* Offer pipelining: receiver side */
    int       offers_sent;
    int       offers_received;

    /* Offer pipelining: sender side */
    int       offer_credits;

    /* Read buffer */
    uint8_t   rbuf[READ_BUF_SIZE];
    size_t    rbuf_len;

    /* Two-priority write queues: high drains first, then low. */
    write_buf_t *wq_hi_head;
    write_buf_t *wq_hi_tail;
    write_buf_t *wq_lo_head;
    write_buf_t *wq_lo_tail;

    uint64_t  bytes_read;  /* cumulative bytes received from this peer */


    /* Address for logging and tracing */
    char      addr_str[64];
    uint32_t  addr_ip;    /* network byte order */
    uint16_t  addr_port;  /* network byte order */
} peer_t;

/* A scheduled payload injection */
typedef struct {
    double   time;
    char     nickname[128];
    uint16_t num_components;
    uint16_t comp_sizes[MAX_COMPONENTS];
} schedule_entry_t;

#define ORACLE_NODE_IDS 256

/* Global node state */
extern struct node_state {
    int         listen_fd;
    int         epoll_fd;
    int         timer_fd;
    uint16_t    listen_port;
    int         node_id;

    peer_t      peers[MAX_PEERS];
    uint64_t    downstream_only_peers;     /* bitmask indexed by node ID (not peer array index);
                                            * max node ID must be < 64 */
    int         num_peers;

    payload_t   payloads[MAX_PAYLOADS];
    int         num_payloads;

    char        node_name[64];

    schedule_entry_t schedule[MAX_PAYLOADS];
    int         schedule_count;
    int         schedule_next;

    double      start_time;   /* CLOCK_MONOTONIC at process start */

    /* Sim-only oracle: BDP and RTmin we'd report if we had a perfect
     * BDP estimator. Indexed by the peer's node_id. Populated at
     * scheduler_peer_hint time from topology config. Consumed by the
     * StartProbe action handler, which installs the oracle values and
     * fires BdpEstimated immediately — see DESIGN.md and bdp_demo/
     * for why a real estimator isn't trivially substitutable. */
    uint64_t    oracle_bdp_bytes[ORACLE_NODE_IDS];
    int         oracle_rtmin_us[ORACLE_NODE_IDS];
} G;

/* ---------------------------------------------------------------------------
 * Functions provided by node.c (infrastructure)
 * ------------------------------------------------------------------------ */

void logmsg(const char *fmt, ...);
int  set_nonblocking(int fd);
void peer_queue_write(peer_t *p, const uint8_t *data, size_t len);
void peer_queue_write_tagged(peer_t *p, const uint8_t *data, size_t len,
                             const uint8_t *payload_hash, uint32_t seqno);
void peer_queue_write_priority(peer_t *p, const uint8_t *data, size_t len);
/* Purge the lo-queue entry matching seqno (skipping the head if partially
 * written). Returns true iff an entry was purged. */
bool peer_purge_seqno(peer_t *p, uint32_t seqno);

/* ---------------------------------------------------------------------------
 * Functions provided by diffusion.c (protocol)
 * ------------------------------------------------------------------------ */

size_t handle_message(peer_t *p, const uint8_t *data, size_t len);
void   inject_scheduled_payload(void);
void   send_request_offer(peer_t *p);
void   send_request_bitmap(peer_t *p, const uint8_t hash[HASH_SIZE],
                           int seqno,
                           const uint8_t *bitmap, size_t bitmap_len);
void   send_cancel_chunk(peer_t *p, int seqno);

#endif /* NODE_H */
