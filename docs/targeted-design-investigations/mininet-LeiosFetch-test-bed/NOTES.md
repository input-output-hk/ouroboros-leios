# Technical Notes

Written by Claude; TODOs iteratively added by humans and resolved by Claude.

## TCP windows

### Send window (congestion window, cwnd)

This controls how many bytes the sender could usefully push into the network before waiting for ACKs.
It starts small (default 10 segments ~ 14 KB) and grows via slow start (doubling each RTT) then congestion avoidance (linear growth).
When loss is detected, it halves.
The cwnd is the sender's estimate of how much the network can absorb without congestion.
Our `initcwnd 200` tuning on some nodes raises the starting point to ~300 KB, skipping most of the slow start phase.

The doubling/linear/halving pattern is the default but not fixed --- Linux supports pluggable congestion control algorithms:

- **Cubic** (Linux default since 2.6.19): uses a cubic function for window growth rather than linear, and reduces to 70% on loss (not 50%).
- **Reno** (classic): the textbook doubling -> linear -> halving.
- **BBR** (Google): abandons loss-based signaling entirely, probes bandwidth and RTT directly, doesn't halve on loss, doesn't do classic slow start.

Slow start doubling is the most standard part --- most algorithms use it or something close.
The congestion avoidance phase and loss response are where they diverge.
Our Mininet hosts use whichever algorithm the Docker container's kernel defaults to (likely Cubic).

### Receive window (rwnd)

This controls how many bytes the receiver is willing to buffer before the sender must stop.
It's advertised in every ACK and reflects the receiver's available socket buffer space.
If the receiver's application is slow to read, rwnd shrinks and throttles the sender.
Our `sysctl tcp_rmem` tuning sets a 16 MB max, and `initrwnd 200` raises the initial advertised window.
In practice, with our single-threaded epoll loop reading promptly, rwnd is rarely the bottleneck.

### Interaction between cwnd and rwnd

The sender must never send more bytes in flight than `min(cwnd, rwnd)`.
Exceeding rwnd is a protocol violation --- the receiver has explicitly said "I can only buffer this much."
A conforming TCP implementation won't do it.
If a buggy sender did, the receiver would likely drop the excess data (no buffer space) and the connection would degrade into retransmission loops.

cwnd can and does exceed rwnd --- they're independent variables.
cwnd is the sender's internal congestion estimate that grows and shrinks based on loss signals.
rwnd is the receiver's advertised limit that changes based on buffer consumption.
TCP uses whichever is smaller as the actual sending limit: `effective_window = min(cwnd, rwnd)`.
So if cwnd grows to 2 MB but rwnd is 500 KB, the sender is limited to 500 KB in flight.
The large cwnd just sits there unused --- it means "the network could handle 2 MB, but the receiver can't."
When rwnd opens back up (the application reads from the socket), the sender can immediately send at the cwnd rate without needing to re-probe the network.

### Why initial sizes matter for link utilization

On a high bandwidth-delay product link (e.g., 50 Mbit x 250 ms RTT = 1.56 MB BDP), the sender can only fill the pipe if cwnd and rwnd are both at least as large as the BDP.
With the default initcwnd of 14 KB, the sender needs `log2(1.56 MB / 14 KB) ~ 7` RTTs of slow start to reach full utilization --- that's 7 x 250 ms = 1.75 seconds of ramping before the link is fully used.
For a 12 MB payload that takes ~2 seconds at full speed, wasting 1.75 seconds on ramp-up nearly doubles the transfer time.
Raising initcwnd to 300 KB cuts the ramp to ~2-3 RTTs, and a large initrwnd ensures the receiver doesn't throttle the sender during this critical early phase.

### Predicted transfer time for 12 MB (no loss, rwnd not a bottleneck)

See `tcp_predict.py` for the model.
It assumes Reno-style slow start (double cwnd each RTT, no loss).
The congestion control algorithm (Reno vs Cubic) doesn't matter here: both use the same slow start, and without loss congestion avoidance never triggers --- slow start runs until cwnd >= BDP, then the link drains at line rate.

#### Default initcwnd (14 KB)

```
RTT \ BW     10 Mbit  20 Mbit  50 Mbit 100 Mbit 250 Mbit 500 Mbit
----------------------------------------------------------------
     2ms      9.60s    4.80s    1.92s    0.96s    0.39s    0.20s
     6ms      9.61s    4.81s    1.93s    0.98s    0.41s    0.22s
    50ms      9.72s    4.96s    2.15s    1.24s    0.72s    0.58s
   100ms      9.92s    5.22s    2.47s    1.61s    1.16s    1.07s
   250ms     10.74s    6.18s    3.62s    2.91s    2.75s    2.75s
```

#### Tuned initcwnd (300 KB)

```
RTT \ BW     10 Mbit  20 Mbit  50 Mbit 100 Mbit 250 Mbit 500 Mbit
----------------------------------------------------------------
     2ms      9.60s    4.80s    1.92s    0.96s    0.39s    0.19s
     6ms      9.61s    4.81s    1.93s    0.97s    0.39s    0.20s
    50ms      9.65s    4.85s    1.97s    1.04s    0.52s    0.37s
   100ms      9.70s    4.90s    2.08s    1.19s    0.74s    0.64s
   250ms      9.86s    5.19s    2.58s    1.85s    1.59s    1.75s
```

#### Tuning benefit (default - tuned)

```
RTT \ BW     10 Mbit  20 Mbit  50 Mbit 100 Mbit 250 Mbit 500 Mbit
----------------------------------------------------------------
     2ms      0.00s    0.00s    0.00s    0.00s    0.00s    0.00s
     6ms      0.00s    0.00s    0.00s    0.01s    0.02s    0.02s
    50ms      0.07s    0.11s    0.18s    0.20s    0.21s    0.21s
   100ms      0.22s    0.32s    0.40s    0.42s    0.42s    0.43s
   250ms      0.88s    0.99s    1.04s    1.06s    1.16s    1.00s
```

At low RTT (2-6ms), tuning has zero benefit --- slow start finishes in 1-2 RTTs regardless.
At high RTT, the benefit scales roughly linearly with RTT: at 50 Mbit, it's 0.18s at 50ms, 0.40s at 100ms, 1.04s at 250ms.
The benefit saturates with bandwidth at a given RTT: at 100ms, going from 50 to 500 Mbit only adds 0.03s more benefit.
The biggest absolute gain is 1.16s at 250ms / 250 Mbit.

### Linux receive buffer tuning

Three sysctls control the receive buffer (and thus rwnd):

**`net.ipv4.tcp_rmem = min default max`** --- three space-separated values in bytes.
- `min` (4096): minimum buffer per socket, guaranteed even under memory pressure.
- `default` (131072): initial buffer for new sockets. Determines the initial rwnd (roughly half this value, ~64 KB).
- `max` (6291456): ceiling for autotuning. The kernel will grow the buffer up to this limit.

**`net.core.rmem_max`** --- hard ceiling for `SO_RCVBUF` set by `setsockopt()`.
If an application explicitly sets `SO_RCVBUF`, it can't exceed this *and* autotuning for that socket is disabled.
Autotuning ignores `rmem_max` and uses `tcp_rmem` max instead.
On modern kernels `net.core.rmem_max` is read-only from a non-init network namespace (a 2024 patch added the read path only), so we cannot raise it from inside Mininet hosts — `sysctl -w` there prints "Operation not permitted" but still exits 0, a silent failure we now catch in `run()`.
Net upshot: we deliberately avoid calling `setsockopt(SO_RCVBUF)` and rely on autotune against `tcp_rmem` max. See `memory/project_tcp_rcvbuf_trap.md` for the debug story.

**Autotuning** is the key feature.
When enabled (the default), the kernel monitors each socket's traffic pattern and grows the receive buffer toward `tcp_rmem` max as needed.
This means rwnd starts at ~64 KB and grows automatically to accommodate high-BDP links without wasting memory on idle sockets.
If the application calls `setsockopt(SO_RCVBUF)`, autotuning is disabled for that socket and the buffer is fixed at the requested size.
Our code does not call `setsockopt(SO_RCVBUF)`, so autotuning remains active.

**Our tuning** sets `tcp_rmem` to `"4096 1048576 16777216"`:
- Initial buffer of 1 MB (rwnd starts at ~500 KB instead of ~64 KB).
- Max of 16 MB (autotuning can grow to include an entire payload).
We do not set `net.core.rmem_max` (it's not writable in our netns) or call `setsockopt(SO_RCVBUF)` (which would disable autotune and then be clamped to the un-raised `rmem_max`).

**Network namespaces** are why this works cleanly in Mininet.
`net.ipv4.tcp_rmem` is a per-network-namespace sysctl, so `sysctl -w` inside a Mininet host only affects that host's namespace.
Each simulated node gets independently tuned TCP parameters --- matching reality, where each machine's operator controls their own sysctl settings.

### ssthresh dynamics across transfers on a persistent connection

Our nodes hold long-lived TCP connections to each peer; multiple application-level payload transfers ride on the same socket.
That makes the kernel's ssthresh state machine relevant to back-to-back payload latencies in a way that single-transfer benchmarks don't expose.

ssthresh is the threshold separating slow-start (cwnd doubles per RTT) from congestion avoidance (cwnd grows ~1 MSS per RTT).
On a steady connection it can only:

- **Decrease on loss.** Cubic sets `ssthresh = 0.7 × cwnd_at_loss` when loss is detected (RTO or 3 dup-ACKs).
  This is the only direct decrease path.
- **Be revised upward at idle restart.** When the connection has been idle and a new send happens, the kernel runs `tp->snd_ssthresh = max(stored_ssthresh, 0.75 × cwnd_at_idle_start)`.
  If cwnd had been growing in CA past the old ssthresh during the previous transfer, this idle bookkeeping is what captures that gain.

Idle restart is the only mechanism that grows ssthresh on a long-lived connection that doesn't experience further loss.

#### When the idle path fires

The kernel's `tcp_cwnd_restart` runs when a new transmit observes that the time since the last send (`jiffies − tp->lsndtime`) exceeds the current RTO.

RTO itself is not a constant.
Linux maintains a smoothed RTT estimate (SRTT) and an RTT variance estimate (RTTVAR) per the Jacobson/Karels formula, updated on every ACK that produces an RTT sample:

```
SRTT   ← (7/8) × SRTT + (1/8) × rtt_sample
RTTVAR ← (3/4) × RTTVAR + (1/4) × |SRTT − rtt_sample|
RTO    ← clamp(SRTT + max(clock_granularity, 4 × RTTVAR), TCP_RTO_MIN, TCP_RTO_MAX)
```

with `TCP_RTO_MIN = 200 ms` and `TCP_RTO_MAX = 120 s`.
On the SoAm-Asia link (155 ms base, 12 ms jitter) the steady-state RTO sits around 500 ms — roughly SRTT ≈ 310 plus 4 × RTTVAR.
Jitter spikes inflate RTTVAR and push RTO higher for several RTTs afterward.
A retransmission doubles RTO via Karn's exponential-backoff rule, and that doubled value persists until the next clean RTT sample updates the estimator.
So whether a given quiet period qualifies as "idle" depends on what RTO happens to be at that moment, which in turn depends on the recent RTT history of the connection.

When the idle test passes, `tcp_cwnd_restart` does roughly:

```c
tp->snd_ssthresh = tcp_current_ssthresh(sk);   // max(stored, 0.75 × cwnd)
restart_cwnd = min(initcwnd_from_route, current_cwnd);
while ((delta -= rto) > 0 && cwnd > restart_cwnd)
    cwnd >>= 1;
cwnd = max(cwnd, restart_cwnd);
```

Two consequences:

1. cwnd is reset toward `initcwnd` from the route (200 on tuned nodes), but only down — never up.
   If pre-idle cwnd was already below the route's initcwnd, the reset is a no-op for cwnd.
2. Pre-idle cwnd survives in the bumped ssthresh, which is what lets the next transfer slow-start to a higher floor.

The "idle" predicate is purely send-side: it checks `lsndtime`, not whether ACKs have been arriving.
So in our protocol, gaps where the connection is exchanging only short OFFER/REQUEST control messages still count as idle once those gaps exceed an RTO.

#### Worked example: `results/keep-ssthresh-carryover-example`

Five 12 MB payloads injected at +5, +25, +45, +65, +85 s on the SoAm-Asia link (40 Mbit, 155 ms ± 12 ms, GE loss).
Per-payload latencies: 5.2 s, 11.9 s, 5.3 s, 8.7 s, 10.7 s.
Payload-2 is the slow outlier; payload-3 is back to fast.

ss snapshots from `node1.ss` show the mechanism:

- During payload-1, a loss burst sets ssthresh to 172 and reduces cwnd to ~174.
- Payload-1 → 2 idle: `max(172, 0.75 × 174) = max(172, 130) = 172`.
  ssthresh stays at 172, cwnd stays at 174.
- Payload-2 starts at cwnd=174, ssthresh=172 — already in CA.
  The link sustains only ~7 Mbit/s out of 40 Mbit/s available; cwnd creeps from 174 to ~342 over the 12 s transfer.
- Payload-2 → 3 idle: at t=44.98 ss shows `cwnd=342 ssthresh=172`; at t=45.20 it shows `cwnd=200 ssthresh=256`.
  `max(172, 0.75 × 342) = 256`; cwnd is reset toward `initcwnd=200`.
- Payload-3 starts with cwnd=200 < ssthresh=256, so it gets one RTT of slow-start to reach 256, then resumes CA from there.

So the slow payload "earned" the next payload's higher floor — but only via the idle-restart bookkeeping.
A workload that kept the connection continuously busy would never see ssthresh ratchet up; it would stay pinned at the post-loss value until a fresh loss reset it lower again.

#### Implications

cubic's ssthresh carryover is realistic; any TCP-based diffusion over a lossy link sees the same handicap.
Three knobs change the dynamics:

- **Switch to BBR** (`net.ipv4.tcp_congestion_control=bbr`).
  BBR doesn't use ssthresh-style backoff; it tracks windowed-max bandwidth and min RTT directly, so prior losses don't depress steady-state throughput.
- **Tear down and reconnect between transfers.**
  Each new connection starts with a fresh ssthresh, at the cost of a handshake RTT per transfer.
- **Accept the carryover as part of the model.**
  If the goal is to characterise what real protocols experience, the slow-recovery tail is part of the answer, and the schedulers should be measured against it.

## Timestamp alignment

Three independent timestamp sources need to share a common x-axis origin in the goodput plots:

1. **pcap traces** (tcpdump on each host interface): packet timestamps in CLOCK_REALTIME, from the kernel.
2. **write traces** (node stdout): binary records with CLOCK_REALTIME wallclock, taken just before each `write()` syscall.
3. **stderr logs** (node stderr): `[node:N <elapsed>]` where `elapsed = CLOCK_REALTIME_now - G.start_time`.

### The epoch approach

Before spawning any nodes, `mininet_topo.py` computes a shared epoch:

```
epoch = time.time() + num_nodes * 0.2 + 1.0
```

This estimates when all nodes will be up and connected (0.2s stagger per node plus 1s margin for TCP handshakes).
The epoch is passed to every node via `--epoch <realtime>` and becomes `G.start_time`.
It is also written to `t0.txt` in the results directory.

Since all nodes share the same `G.start_time`, schedule times are synchronized: `schedule_time=5.0` fires at the same wall-clock moment on every node.
Early log lines (during startup, before the epoch) have negative elapsed times, which is correct and informative.

### Alignment in the plot script

The plot script reads the epoch from `t0.txt` and uses it as the x-axis origin for all three sources:

- **pcap/write traces**: `x = wallclock - epoch`.
- **stderr events**: `x = elapsed` (directly, since `elapsed = wallclock - epoch` by construction).

No cross-source correlation or heuristic offset estimation is needed.

## Middlebox-based network emulation

Each edge `(A, B)` in the topology is materialised as a Mininet host `mbN` sitting between A and B, linked by two veth pairs.
End hosts A and B have no shaping of their own; all rate-limiting, AQM, and propagation delay live on the middlebox and the adjacent veths.

```
  host A  ──[netem]── mbN ──[htb + fq_codel]── host B
```

Each host carries its identity as `10.0.0.<node_id>/32` on `lo`, while every veth pair gets its own `/24` subnet.
Static routes and `src`-pinned entries ensure that a packet to `10.0.0.<peer>` transits the middlebox and emerges with source `10.0.0.<self>`, preserving node-identity-by-IP at the receiver.
Each middlebox enables `net.ipv4.ip_forward`.

### Why this much complexity

The straightforward alternative is a single Linux bridge with every host attached and all tc chains on the hosts' own egress interfaces.
That setup forces per-peer HTB classes on one root qdisc per interface, which in turn forces `netem` to live at the class level — *above* any leaf-slot AQM.
Netem's large packet buffer then becomes the real bottleneck queue, shielding the AQM from the backpressure it was designed to respond to.

With the bridged layout, cubic never sees timely loss signals from fq_codel.
Its cwnd grows until `tcp_wmem[2]`-capped sndbuf auto-tune stops chasing or netem's `limit` overflows — typically multi-megabytes of uncancellable in-flight data, resulting in `MSG_CANCEL_CHUNK` arriving "too late" for dozens of chunks after a payload completes.

The middlebox moves the bottleneck queue onto a dedicated interface with only one peer's traffic.
That single-peer simplicity lets `htb + fq_codel` work as the bottleneck queue *with* AQM, while `netem` is pushed to a different interface altogether (the host's propagation-only veth).
Cubic gets real drop signals at the correct moment; sndbuf stays near BDP; cancellation is no longer chronically late.

The price is the extra plumbing — `N_edges` middleboxes, `2 × N_edges` veth pairs, `2 × N_edges` /24 subnets, per-host routes, and IP forwarding on each middlebox.
We accept that because the alternative makes our AQM behaviour unfaithful to how real ISP-edge devices absorb traffic.
