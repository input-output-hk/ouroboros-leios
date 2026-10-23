# Receiver-side TCP BDP visibility demo

A minimal self-contained C program that connects to an HTTP server, downloads
a file, and records one sample per `read()` syscall.
The aim is to show how messy the raw receiver-side TCP arrival signal is —
much messier than the naive "bytes per second" mental model would suggest.

No TLS, no dependencies beyond libc. Runs on any modern Linux.

## Why this demo is set up the way it is

The whole point is to show the *inevitable* challenges of receiver-side
BDP measurement — not artifacts of a sloppy client. So the demo goes
to some lengths to take itself out of the picture:

1. **Synchronous blocking `read()`**, no epoll. Our process has
   nothing else to do while waiting; an event loop would just add a
   user-space wakeup step with no benefit.
2. **`SO_RCVBUF = 16 MB`** — takes receiver-side TCP flow-control off
   the table, so the kernel never pauses the sender because our app
   was "slow" to read.
3. **`SO_BUSY_POLL = 50 µs`** — the kernel busy-polls the NIC for
   50 µs before sleeping, cutting NIC-interrupt → thread-wakeup
   latency to a small constant.
4. **`SCHED_FIFO` real-time scheduling** — the thread isn't preempted
   by other work while it's waiting for bytes.
5. **Pinned to CPU 0** (`sched_setaffinity`) — no cache migrations or
   IRQ-chasing costs during the run.

If the dataset still looks messy under this setup, then what it's
showing really is inherent to the network path + peer + TCP-stack
behavior, not to the observer.

## Build

```sh
cc -O2 -o demo_bdp demo_bdp.c
```

## Run

```sh
sudo ./demo_bdp <host> <port> <path> [max_bytes] > run.csv
```

`sudo` is recommended so items (3)-(5) actually take effect. Without
privileges the program still runs and prints warnings for the options
it couldn't apply; the data is still useful, just slightly more
jittered by client-side scheduling.

The CSV has one row per `read()` call, with columns
`t_s, bytes_this_read, cum_bytes, tcpi_rtt_us, tcpi_delivery_rate_bps`.

## Endpoints that serve plain HTTP without redirecting

These have been verified to respond with an HTTP 200 body (no 301/302 to HTTPS).
You may want to cap with `max_bytes` since many of these files are large.

```sh
./demo_bdp speedtest.london.linode.com 80 /100MB-newyork.bin 10000000 > linode.csv
./demo_bdp mirror.math.princeton.edu 80 /pub/archlinux/iso/latest/archlinux-x86_64.iso 10000000 > princeton.csv
./demo_bdp ftp.uni-kl.de 80 /pub/linux/archlinux/iso/latest/archlinux-x86_64.iso 10000000 > kl.csv
```

The public HTTP-speedtest-server ecosystem has been shrinking as HTTPS
becomes universal, so keep a curl spot-check in mind: if a chosen
endpoint starts returning a `301` redirect to HTTPS, or a small HTML
stub instead of binary content, swap it out. Search
<https://github.com/topics/speedtest-server> for more.

Endpoints verified to serve real binary content over HTTP at time of
writing (double-check with `curl -sI`):

- `speedtest.london.linode.com` (UK, Linode backbone) — `/100MB-newyork.bin`,
  `/100MB-frankfurt.bin`, `/100MB-tokyo.bin`, … Run against multiple
  region files from the same host to see the arrival pattern change
  dramatically with distance.
- `mirror.math.princeton.edu` (Princeton University, US) —
  `/pub/archlinux/iso/latest/archlinux-x86_64.iso` (~1.5 GB).
- `ftp.uni-kl.de` (University of Kaiserslautern, Germany) —
  `/pub/linux/archlinux/iso/latest/archlinux-x86_64.iso` (~1.5 GB).

For lower-bandwidth endpoints (demo variety):

- `speedtest.tele2.net` (Sweden) — `/10MB.zip`, `/100MB.zip`, `/1GB.zip`, …
- `ipv4.download.thinkbroadband.com` (UK) — `/20MB.zip`, `/50MB.zip`, `/200MB.zip`, …

## Rigor mode: run your own sender (`demo_server` + `--raw`)

Public HTTP endpoints come with sender-side variability we can't
measure or control — rate limiting, request-prioritization, slow
servers, redirects, middleboxes. To pin down the *receiver-side*
challenges alone, stand up a controlled sender.

The companion `demo_server.c` is a ~40-line TCP server that accepts a
connection, immediately pushes N bytes of a pre-allocated pattern as
fast as the kernel accepts, and closes. No HTTP, no protocol
preamble — the accept completion is also the start of bulk data.

### Build & run the server

```sh
cc -O2 -o demo_server demo_server.c
./demo_server 9000 104857600            # serves 100 MB per connection
```

Run it on a well-provisioned VPS (Linode, DigitalOcean, Hetzner — a
$5/mo tier usually has a 1 Gbps NIC; $40/mo has 10 Gbps).

### Use it from the client

```sh
sudo ./demo_bdp --raw <server_host> 9000 '' 10000000 > rigor.csv
```

`--raw` skips the HTTP GET; the client just reads bytes on connect.
The `<path>` argument is ignored in raw mode but still positional —
pass `''` as a placeholder.

### Why rigor mode makes a stronger demo

- **Deterministic sender.** No unknown rate policy. Whatever you see
  is from the network + your kernel's receive side.
- **Any bandwidth you pay for.** Scales cleanly with server NIC.
- **You can show sender-side variations intentionally.** E.g., run
  two servers side-by-side with different TCP congestion control
  (`sysctl net.ipv4.tcp_congestion_control=bbr` vs `cubic`) and
  measure identical-client traces against each — produces a striking
  visual difference on the same network path.

## Plot

Requires matplotlib. Any one of:

```sh
pip install matplotlib                 # if you have pip
nix-shell -p python3Packages.matplotlib --run 'python3 plot.py *.csv plots/'
```

Per-run PNG shows four panels:

1. Cumulative bytes vs. time — the ramp shape of slow-start and
   eventual steady-state.
2. Per-read rate in MB/s — instantaneous arrival rate. Note how much
   variance sits on top of a nominally steady transfer.
3. Read-size histogram over time (log-scale KB) — kernel batching
   (GRO) concentrates many network packets into a single `read()`.
4. `tcpi_rtt` in ms — queueing inflates during bulk transfer;
   correlations with rate dips hint at loss recovery.

The plot's title flags whether `tcpi_delivery_rate` was ever non-zero.
In practice you'll often see a small *non-zero* constant — but it
reflects *your tiny outbound request's* delivery rate (a few hundred
bytes over the initial RTT = single-digit Kbps), not the download.
The kernel's delivery-rate estimator is fed by ACK timing of data
*you* sent; it has no data on the peer's sending rate to you.
Functionally it's still useless for the receiver-side BDP question.

## Things to look for across runs

- **Slow-start shape**: some servers ramp cleanly to a sustained rate,
  others oscillate, others plateau well below link capacity.
- **Stall bins**: gaps of 10s to 100s of ms where nothing arrives.
  Loss recovery, transient queueing, or server-side pauses all look
  the same from the receiver.
- **GRO/batching bursts**: per-read rate spikes of 10× the sustained
  rate when the kernel delivers a bundle of packets at once.
- **RTT inflation**: `tcpi_rtt` climbs above the nominal path RTT
  during bulk transfer; drops correlate with rate recovery.
- **`tcpi_delivery_rate = 0`**: the exposed TCP delivery-rate
  estimator is fed by the sender's ACK-timing rate sampler, so the
  receiver has no analogous reading.

These are exactly the signals that make a "just measure BDP on the
receiver" idea harder than it appears.

## Why `SO_RCVBUF` is set large

The demo sets `SO_RCVBUF` to 16 MB unconditionally. Without it, Linux's
default receive-side flow-control can advertise a smaller rcv-window
during bulk transfer, throttling the sender for reasons unrelated to
the network itself. We're trying to see *the network*, not our own
kernel's flow control, so we remove that variable.

This is also the right thing to do in any application that plans to do
its own receiver-side flow-control or BDP reasoning.
