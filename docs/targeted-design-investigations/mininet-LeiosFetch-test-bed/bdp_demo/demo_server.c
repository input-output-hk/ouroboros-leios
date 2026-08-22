/*
 * demo_server.c — minimal companion to demo_bdp.
 *
 * Listen on a TCP port. For each incoming connection, immediately
 * write <send_bytes> bytes from a pre-allocated buffer as fast as
 * the kernel accepts, then close. No HTTP, no protocol handshake:
 * the accept-completion instant is also the start-of-bulk-data
 * instant, giving the client a clean timing origin.
 *
 * The client's --raw flag skips its HTTP GET and just reads.
 *
 * Why this exists: public HTTP endpoints vary in sender-side
 * behavior, rate limiting, and response-preamble overhead. When
 * demonstrating receiver-side TCP challenges, a controlled sender
 * removes all of that variability, so any remaining noise in the
 * client's trace is genuinely from the network path + client-kernel
 * receive behavior.
 *
 * Build: cc -O2 -o demo_server demo_server.c
 * Run  : ./demo_server <port> <send_bytes>
 * Example: ./demo_server 9000 104857600   # serves 100 MB per conn
 */

#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <errno.h>

#include <sys/socket.h>
#include <sys/signal.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s <port> <send_bytes>\n", argv[0]);
        return 2;
    }
    int port = atoi(argv[1]);
    size_t send_bytes = strtoull(argv[2], NULL, 10);
    if (send_bytes == 0) {
        fprintf(stderr, "send_bytes must be > 0\n");
        return 2;
    }

    /* Ignore SIGPIPE so a client disconnecting mid-write doesn't kill us. */
    signal(SIGPIPE, SIG_IGN);

    /* Pre-allocate the payload once. Contents don't matter for the
     * demo; using a fixed pattern avoids any per-connection setup
     * cost and makes the server's only job be write(). */
    uint8_t *buf = malloc(send_bytes);
    if (!buf) { perror("malloc"); return 1; }
    memset(buf, 0xA5, send_bytes);

    int srv = socket(AF_INET, SOCK_STREAM, 0);
    if (srv < 0) { perror("socket"); return 1; }

    int one = 1;
    setsockopt(srv, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    struct sockaddr_in addr = {0};
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = INADDR_ANY;
    addr.sin_port = htons(port);
    if (bind(srv, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        perror("bind"); return 1;
    }
    if (listen(srv, 16) < 0) { perror("listen"); return 1; }

    fprintf(stderr, "demo_server: listening on :%d, %zu bytes per conn\n",
            port, send_bytes);

    for (;;) {
        struct sockaddr_in peer;
        socklen_t peer_len = sizeof(peer);
        int c = accept(srv, (struct sockaddr *)&peer, &peer_len);
        if (c < 0) {
            if (errno == EINTR) continue;
            perror("accept"); break;
        }

        /* Keep the kernel's send buffer shallow enough that write()
         * backpressure actually reflects network progress. Turn off
         * Nagle so writes land promptly even for tiny tails. */
        int on = 1;
        setsockopt(c, IPPROTO_TCP, TCP_NODELAY, &on, sizeof(on));

        char peer_ip[INET_ADDRSTRLEN];
        inet_ntop(AF_INET, &peer.sin_addr, peer_ip, sizeof(peer_ip));
        fprintf(stderr, "conn from %s:%d — sending %zu bytes\n",
                peer_ip, ntohs(peer.sin_port), send_bytes);

        size_t left = send_bytes;
        const uint8_t *p = buf;
        while (left > 0) {
            ssize_t w = send(c, p, left, 0);
            if (w < 0) {
                if (errno == EINTR) continue;
                if (errno == EPIPE || errno == ECONNRESET) break;
                perror("send"); break;
            }
            p += w;
            left -= (size_t)w;
        }
        close(c);
    }

    close(srv);
    free(buf);
    return 0;
}
