/*
 * demo_bdp.c — receiver-side TCP BDP visibility demo.
 *
 * A minimal client that opens a TCP connection, sends a bare HTTP/1.0
 * GET, and records one sample per read() syscall. Dumps all samples as
 * CSV on stdout.
 *
 * The demo is intentionally configured so that the remaining noise can
 * only come from *inevitable* sources — network path, peer, GRO,
 * kernel-level TCP behavior — and not from our own client being a
 * slow or suboptimal reader. Specifically:
 *
 *   1. Synchronous blocking read() (no epoll). The process has nothing
 *      else to do, so there is no reason to wait for a user-space event
 *      loop to schedule a read.
 *   2. SO_RCVBUF set to 16 MB — removes receiver-side flow-control
 *      throttling from the picture.
 *   3. SO_BUSY_POLL=50 — the kernel busy-polls the NIC for 50 µs
 *      before sleeping, cutting interrupt-and-wakeup latency.
 *   4. SCHED_FIFO priority — the thread is not preempted by other
 *      work while waiting for bytes.
 *   5. CPU affinity pinned to core 0 — avoids cache migration and
 *      IRQ-chasing costs.
 *
 * If any of (3)-(5) fail (permissions), we log a warning and continue;
 * the demo still produces useful data, just with slightly more
 * client-side jitter in the tail of the per-read timing distribution.
 *
 * Build: cc -O2 -o demo_bdp demo_bdp.c
 * Run  : sudo ./demo_bdp <host> <port> <path> [max_bytes]
 *        (privilege is needed for SCHED_FIFO, SO_BUSY_POLL above sysctl
 *         limit, and CPU affinity of real-time threads on some systems)
 */

#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <errno.h>
#include <time.h>
#include <sched.h>

#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <linux/tcp.h>

#ifndef SO_BUSY_POLL
#define SO_BUSY_POLL 46
#endif

#define READ_BUF_SIZE      (256 * 1024)
#define RCVBUF_BYTES       (16 * 1024 * 1024)   /* keep receive flow-control out of the way */
#define BUSY_POLL_US       50                   /* NIC busy-poll before sleep */
#define FIFO_PRIORITY      10
#define PIN_CPU            0
#define MAX_SAMPLES        1000000

typedef struct {
    double   t;                         /* seconds since start of transfer */
    size_t   n_bytes;                   /* bytes returned by this read() */
    uint64_t cum_bytes;                 /* running total */
    uint32_t tcpi_rtt_us;               /* smoothed RTT per kernel */
    uint64_t tcpi_delivery_rate_bps;    /* sender-side metric; usually useless on receiver */
} sample_t;

static sample_t samples[MAX_SAMPLES];
static int n_samples = 0;

static double elapsed_since(const struct timespec *t0) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (now.tv_sec - t0->tv_sec) + (now.tv_nsec - t0->tv_nsec) / 1e9;
}

static void setup_realtime_environment(void) {
    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET(PIN_CPU, &set);
    if (sched_setaffinity(0, sizeof(set), &set) < 0)
        fprintf(stderr, "warn: sched_setaffinity(cpu=%d) failed: %s\n",
                PIN_CPU, strerror(errno));

    struct sched_param sp = { .sched_priority = FIFO_PRIORITY };
    if (sched_setscheduler(0, SCHED_FIFO, &sp) < 0)
        fprintf(stderr, "warn: sched_setscheduler(SCHED_FIFO) failed: %s"
                        " (hint: run as root)\n", strerror(errno));
}

int main(int argc, char **argv) {
    /* Parse a possible --raw flag (skips HTTP preamble, for use with
     * the companion demo_server). */
    int raw_mode = 0;
    int argi = 1;
    while (argi < argc && argv[argi][0] == '-') {
        if (strcmp(argv[argi], "--raw") == 0) { raw_mode = 1; argi++; continue; }
        fprintf(stderr, "unknown flag: %s\n", argv[argi]);
        return 2;
    }
    if (argc - argi < 3) {
        fprintf(stderr,
            "Usage: %s [--raw] <host> <port> <path> [max_bytes]\n"
            "\n"
            "HTTP mode (default): sends an HTTP/1.0 GET for <path>.\n"
            "  Example: %s speedtest.tele2.net 80 /10MB.zip 10000000\n"
            "\n"
            "--raw: no HTTP; just read bytes on connect. Use with demo_server.\n"
            "  Example: %s --raw my.vps 9000 '' 10000000\n"
            "\n"
            "Note: run under sudo to exercise SCHED_FIFO, SO_BUSY_POLL,\n"
            "      and CPU pinning fully.\n",
            argv[0], argv[0], argv[0]);
        return 2;
    }
    const char *host = argv[argi + 0];
    const char *port = argv[argi + 1];
    const char *path = argv[argi + 2];
    uint64_t max_bytes = (argc - argi >= 4) ? strtoull(argv[argi + 3], NULL, 10) : (uint64_t)-1;

    setup_realtime_environment();

    struct addrinfo hints = {0}, *res = NULL;
    hints.ai_family   = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    int rc = getaddrinfo(host, port, &hints, &res);
    if (rc != 0) {
        fprintf(stderr, "getaddrinfo(%s:%s): %s\n", host, port, gai_strerror(rc));
        return 1;
    }

    int fd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (fd < 0) { perror("socket"); return 1; }

    int rcvbuf = RCVBUF_BYTES;
    if (setsockopt(fd, SOL_SOCKET, SO_RCVBUF, &rcvbuf, sizeof(rcvbuf)) < 0)
        fprintf(stderr, "warn: SO_RCVBUF failed: %s\n", strerror(errno));

    int bp = BUSY_POLL_US;
    if (setsockopt(fd, SOL_SOCKET, SO_BUSY_POLL, &bp, sizeof(bp)) < 0)
        fprintf(stderr, "warn: SO_BUSY_POLL=%d failed: %s\n",
                bp, strerror(errno));

    if (connect(fd, res->ai_addr, res->ai_addrlen) < 0) {
        perror("connect"); return 1;
    }
    char peer_str[INET6_ADDRSTRLEN] = {0};
    if (res->ai_family == AF_INET) {
        struct sockaddr_in *sa = (struct sockaddr_in *)res->ai_addr;
        inet_ntop(AF_INET, &sa->sin_addr, peer_str, sizeof(peer_str));
    } else if (res->ai_family == AF_INET6) {
        struct sockaddr_in6 *sa = (struct sockaddr_in6 *)res->ai_addr;
        inet_ntop(AF_INET6, &sa->sin6_addr, peer_str, sizeof(peer_str));
    }
    freeaddrinfo(res);

    /* HTTP mode: send an HTTP/1.0 GET with Connection: close (server
     * signals EOF by closing), Accept-Encoding: identity (no gzip, so
     * byte counts are honest). Raw mode sends nothing — the companion
     * demo_server starts pushing the moment accept() completes. */
    if (!raw_mode) {
        char request[2048];
        int req_len = snprintf(request, sizeof(request),
            "GET %s HTTP/1.0\r\n"
            "Host: %s\r\n"
            "User-Agent: bdp-demo/1.0\r\n"
            "Accept-Encoding: identity\r\n"
            "Connection: close\r\n"
            "\r\n", path, host);

        for (ssize_t sent = 0; sent < req_len; ) {
            ssize_t w = send(fd, request + sent, (size_t)(req_len - sent), 0);
            if (w < 0) {
                if (errno == EINTR) continue;
                perror("send"); return 1;
            }
            sent += w;
        }
    }

    struct timespec t0;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    uint64_t cum_bytes = 0;
    static char buf[READ_BUF_SIZE];

    /* Blocking synchronous read. The kernel wakes us the moment data
     * is available; with SO_BUSY_POLL the wakeup path is busy-polled
     * rather than interrupt-driven, minimizing latency. */
    for (;;) {
        ssize_t n = read(fd, buf, sizeof(buf));
        if (n == 0) break;                  /* EOF */
        if (n < 0) {
            if (errno == EINTR) continue;
            perror("read"); break;
        }
        cum_bytes += (uint64_t)n;
        double t = elapsed_since(&t0);

        struct tcp_info ti;
        socklen_t ti_len = sizeof(ti);
        memset(&ti, 0, sizeof(ti));
        getsockopt(fd, IPPROTO_TCP, TCP_INFO, &ti, &ti_len);

        if (n_samples < MAX_SAMPLES) {
            samples[n_samples++] = (sample_t){
                .t                       = t,
                .n_bytes                 = (size_t)n,
                .cum_bytes               = cum_bytes,
                .tcpi_rtt_us             = ti.tcpi_rtt,
                .tcpi_delivery_rate_bps  = ti.tcpi_delivery_rate,
            };
        }

        if (cum_bytes >= max_bytes) break;
    }

    printf("# host=%s port=%s path=%s mode=%s peer_ip=%s cum_bytes=%llu samples=%d\n",
           host, port, path, raw_mode ? "raw" : "http", peer_str,
           (unsigned long long)cum_bytes, n_samples);
    printf("t_s,bytes_this_read,cum_bytes,tcpi_rtt_us,tcpi_delivery_rate_bps\n");
    for (int i = 0; i < n_samples; i++) {
        printf("%.6f,%zu,%llu,%u,%llu\n",
               samples[i].t,
               samples[i].n_bytes,
               (unsigned long long)samples[i].cum_bytes,
               samples[i].tcpi_rtt_us,
               (unsigned long long)samples[i].tcpi_delivery_rate_bps);
    }

    close(fd);
    return 0;
}
