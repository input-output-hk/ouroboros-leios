# Fetch Strategy Design

## Problem statement

A node pulling a large payload (12 MB, ~1500 components) from multiple peers must decide what to request from whom and when.
The extremes of the policy space are pinned by two baseline schedulers:

- **OnePeerScheduler**: request the whole payload from the first peer that offered. Minimal bandwidth, catastrophic tail latency.
- **FullHedgeScheduler**: request every chunk from every offering peer, with cancellation racing the wire as deliveries arrive. Maximal tail protection, 2× bandwidth waste.

See ANALYSIS.md for head-to-head numbers on `topo-8-1` with co-injection: FullHedge has real duplicate-cancellation costs (~97 MB wire traffic for a 24 MB payload-pair), and OnePeer's latency is ~5× worse than either alternative.

The goal is a smarter scheduling policy that reduces wasted bandwidth without pessimizing tail latency.
The right balance between these two depends on network conditions (only partially observable) and on the operator's own cost model, which may vary over time.
The policy must therefore be parameterized over this trade-off, not hardcoded to a single balance point.

## Chunking

When the manifest arrives, the node partitions its missing components into chunks of roughly 64 KB.
A 12 MB payload yields ~187 chunks.
Chunks are the unit of scheduling — all policy decisions operate on chunks, not individual components.

When sending MSG_REQUEST for a chunk, the node may trim components already received (an optimization not visible to the scheduling layer).
MSG_CANCEL_CHUNK targets a specific chunk at a specific peer, enabling targeted cancellation as soon as a chunk completes rather than waiting for the whole payload.

## Dynamics of a fetch

Consider `topo-8-1`: eight source nodes, each with a heterogeneous bandwidth/delay/loss link to a single Sink.

![topology](results/mb-8-1/topology.png)

### Evolving options

The Sink's options change over the fetch window.
At first it has one peer that has offered and no information about anyone's link quality.
As more peers offer, it has up to 8 peers with varying amounts of delivery history.
Offer arrival order does not predict link quality — a peer can win the handshake race and still be the slowest link.

We can also model a single payload reaching different nodes at different times via schedule co-injection (see `input.json.md`): listing the same components under an array of `(time, node)` pairs gives each node the same payload hash at the time we specify, simulating staggered upstream arrivals without needing topology links upstream of the sources.

### The request-response feedback loop

1. Assign chunk(s) to peer.
2. Peer receives the REQUEST, starts sending RESPONSE.
3. RESPONSE traverses the link (propagation delay + transmission time + possible loss/retransmit).
4. Node 12 receives the chunk. It now has a throughput sample for that peer and can assign more work.

The minimum round-trip of this loop is: request propagation + chunk transmission + response propagation.

### Pipeline depth

If only one chunk is in flight per peer, the link goes idle for a full RTT between each delivery.
Multiple chunks must be in flight to keep the link saturated — the target is the link's bandwidth-delay product (BDP) divided by the chunk size.
A 50 Mbit link with 50ms RTT has a BDP of ~312 KB, requiring roughly 5 in-flight chunks.

This is an estimate the policy must continuously maintain — it depends on the peer's observed RTT and throughput, which change over the lifetime of the connection and possibly mid-transfer.

Too shallow a pipeline wastes time (link idle, extending tail latency).
Too deep a pipeline wastes scheduling opportunity — chunks queued behind a slow peer's backlog could have been assigned to a faster peer.
However, `TCP_NOTSENT_LOWAT` on the sender side mitigates the wire-bytes cost of over-assignment: it keeps the kernel send buffer shallow, so excess data remains in the application-level write queue where MSG_CANCEL_CHUNK can purge it.
BDP is therefore a target to aim for, not a hard ceiling — overshooting is recoverable, undershooting is not.

## Available information

### TCP_INFO

Rather than implementing our own estimation, we can query the kernel's per-socket TCP statistics via `getsockopt(TCP_INFO)`:

| Signal | TCP_INFO field | What it tells us |
|--------|---------------|------------------|
| Loaded RTT | `tcpi_rtt` | Smoothed RTT (µs), updated on every ACK |
| RTT variance | `tcpi_rttvar` | How stable the link is |
| Baseline RTT | `tcpi_min_rtt` | Minimum observed RTT (propagation floor) |
| Loss | `tcpi_lost` | Segments kernel considers lost |
| Retransmissions | `tcpi_retrans` | Segments currently being retransmitted |

The kernel maintains these estimates as long as data flows on the socket.
No additional protocol messages are needed.

Conspicuously absent from this table: `tcpi_snd_cwnd` and `tcpi_unacked`.
These describe *our* send-side state, not the peer's.
In a pull-based protocol we only transmit tiny MSG_REQUESTs, so our send cwnd is pinned at the kernel's initial window (~14.5 KB) forever and our in-flight-bytes is always ~zero.
The peer's send cwnd — the thing that actually governs delivery rate to us — is internal to the peer's kernel and not observable from our socket.
See "BDP estimation" below for how we work around this.

### Derived signals

- **Queue delay** = `tcpi_rtt` - `tcpi_min_rtt`. Persistent growth indicates bufferbloat on the path — a signal to reduce pipeline depth to that peer.
- **Stall detection**: a spike in `tcpi_lost` or `tcpi_retrans`, or a sudden RTT increase, indicates the link has entered a degraded state. Real Internet loss is bursty (router buffer overflows, congestion events, transient path failures); our Mininet setup approximates this with netem's Gilbert-Elliott model, but the policy should handle the general phenomenon rather than being tuned to any specific loss model.

## BDP estimation

> **Current status**: the simulator ships with an **oracle stub** that reads each peer's BDP and min-RTT straight from the topology config and fires `BdpEstimated` after a configurable delay (see `scheduler_bridge.c`).
> The full burst-probe design below is retained as the target for when we replace the stub with a real estimator.
> See `bdp_demo/` for why receiver-side BDP measurement on bursty TCP is non-trivial in practice.

### Why this needs its own section

An earlier revision of this document assumed BDP could be read off TCP_INFO directly as `tcpi_snd_cwnd × tcpi_snd_mss`.
That was wrong for the reason noted above: on a download socket in a pull protocol, our send cwnd is meaningless.
The peer's send cwnd is the load-bearing quantity and is not exposed to us.
What *is* observable from our side: RTT (via `tcpi_rtt`, driven by our MSG_REQUEST/ACK exchange), and received bytes over time.

### Why passive rate measurement isn't enough

The natural next idea — track received bytes per unit time as a throughput estimate, then compute BDP = throughput × RTT — has a subtle trap.
When pipeline depth is shallow (one chunk at a time), the apparent rate is `chunk_size / (RTT + chunk_size / link_rate)`, which is strictly less than `link_rate`.
Multiplying the under-estimated rate by RTT gives an under-estimated BDP.
Using that BDP to set pipeline depth produces a still-shallow pipeline.
The loop is self-reinforcing: there is no way to discover a higher link rate by measuring a regime where we are capping ourselves.

### Why not just send the burst and read `tcpi_bytes_received` at the end?

Tempting: queue a big burst, wait for it to drain, divide total bytes by total elapsed time, call that the link rate.
This fails for reasons that are instructive.

The burst has three regimes:
- **Slow-start ramp**: peer's cwnd grows from IW=10 segments, doubling per RTT until it reaches BDP. Delivery rate during this phase is strictly below link rate and is non-stationary.
- **Plateau**: peer's cwnd has reached BDP, peer is saturating the bottleneck, delivery rate = link rate. This is the only regime where the measurement is trustworthy.
- **Drain tail**: once we stop issuing new requests (either because the burst runs out or we've canceled overshoot), the pipeline empties. The last chunks arrive in a single-chunk regime again, with inter-chunk gaps widening.

Averaging `bytes_received / elapsed_time` over the whole burst mixes all three regimes and systematically underestimates link rate.
Reading `tcpi_bytes_received` at a single instant tells you a cumulative total, not a rate — you need two samples to get a rate, and both of them need to be *inside the plateau*.
Worse, you don't know a priori where the plateau starts and ends; that's precisely what the measurement is supposed to discover.

The correct signal is the *shape* of cumulative-bytes-over-time, not its endpoints.
The shape tells you when the ramp ended and (if you watch long enough) when the drain starts; the slope during the plateau is the number you want.
Plateau detection therefore requires multiple rate samples observed throughout the burst — which is what per-chunk arrival sampling gives us, for free, via the events the scheduler already receives.

A variant that *would* work: poll `tcpi_bytes_received` on a frequent timer during the burst to reconstruct the same cumulative-bytes-over-time curve from TCP_INFO rather than application-layer events.
That's just a different data source for the same algorithm.
We use per-chunk events because they arrive at the natural granularity of our control loop (we act on `ChunkDelivered`, not on a timer), and because `tcpi_bytes_received` polls give the same information an instant later (bytes arrive in the receive buffer, are delivered to userspace, and `p->bytes_read` is updated — any meaningful divergence between that counter and `tcpi_bytes_received` is a bug we'd want to know about independently).

### The "seismic imaging" approach

We borrow the algorithmic skeleton of BBR (Bottleneck Bandwidth and RTT) but drop its continuous-rate-estimation machinery in favor of discrete burst probing.
The analogy: to image subsurface geology, set off a stick of dynamite at a known time and listen for echoes.
To measure a peer's BDP, emit a deliberately large burst of requests and watch the arrival rate climb until it plateaus.
A plateau, at a moment when the peer demonstrably has backlog, is trustworthy: the peer is saturating *something*, so its send rate = link rate.
BDP = plateau rate × minimum RTT observed during the burst.

The measurement is only meaningful during a burst.
We do not passively re-estimate BDP from steady-state arrivals, because in steady state we are pacing at roughly BDP and the "apparent rate" measurement becomes ambiguous with self-pacing.

Operationally this looks like BBR's Startup phase (probe-ramp-plateau), Drain (cancel the overshoot), Cruise (hold steady at measured BDP), and occasional ProbeBW (gentle re-probe to detect link changes) — but made coarser to match our chunk-granularity control surface.

### Per-peer state machine

- **Unknown** (initial, and after snub-recovery): no BDP estimate.
  On the next workload assigned to this peer, emit a burst sized to keep them non-app-limited through several RTTs of slow-start doubling.
  First-probe default: 2 MB (≈ 32 chunks), rationale: TCP slow-start doubles cwnd per RTT from IW=10 segments (~14.5 KB), so reaching a BDP of ~1 MB takes ~7 RTTs and the cumulative bytes delivered during the ramp are ≈ 2× final cwnd.
  2 MB covers typical access-link BDPs with headroom.
  If the burst drains without a plateau being detected, the peer's BDP is at least as large as this probe — next probe doubles (4 MB, 8 MB, …).

- **Probing**: burst is outstanding.
  Per chunk delivered, compute instantaneous rate `chunk_size / inter_arrival_gap` and update the running min of `tcpi_rtt` (the queue-free RTT floor, cleanest early in the burst).
  **Plateau detected** when three consecutive per-chunk rates all show growth ratio < 1.1 (within 10% jitter, no further climb).
  At plateau: `BDP = plateau_rate × RTmin`; cancel outstanding requests beyond the estimated "already-on-wire" threshold (cancel-prediction lemma below); transition to Known.

- **Known**: BDP estimate available.
  Pipeline depth target = BDP (steady-state), possibly slightly over to guarantee non-app-limited operation.
  On periodic re-probe: queue 1.5× BDP worth of extra chunks for ~3 RTTs; if observed rate climbs, raise BDP estimate; otherwise cancel excess and stay.
  Re-probe cadence: ≥ 60 s wall-clock *and* ≥ 10 MB transferred since last probe.
  On stall/snub: drop back to Unknown via existing Probationary/Snubbing backoff machinery.

### Cancel-prediction lemma

When plateau is detected at time t_d during a probe that began at t_0:
- Observed steady rate R ≈ peer's send rate (valid because peer has been non-app-limited).
- Our MSG_CANCEL_CHUNK reaches the peer at t_d + RTT/2.
- By then the peer will have sent ≈ R · (t_d + RTT/2 − t_0) bytes.
- An outstanding request at cumulative queue position P is still purgeable iff P > R · (t_d + RTT/2 − t_0); anything below that threshold is already on the wire and we should not waste a CANCEL.

We issue CANCELs only for predicted-purgeable requests and release their capacity on receipt of MSG_CANCELED_RESPONSE (the existing protocol).
Requests predicted to already be on the wire are left to deliver normally.

### What about observing peer-side bandwidth directly?

The peer's TCP exposes `tcpi_delivery_rate` on *their* socket, computed by their RACK-driven rate sampler from the ACK stream of data they sent.
That field is zero on our side because the rate sampler is only fed from the sender's path.
No standard TCP mechanism exposes the sender's cwnd or delivery rate to the receiver.

Moreover, even if `tcpi_delivery_rate` were somehow readable from our side, it wouldn't suffice for the burst-probe design.
The kernel computes it as a max-filter over a sampling window whose length is set internally (BBR uses 6–10 RTTs) and not exposed through any socket option.
We can't ask for "the rate over the last 500 ms" or "the rate right now"; we get whatever the kernel's filter has decided is representative.
For continuous-rate-adaptation congestion control that's fine, but the burst-probe wants to detect a *sharp transition* — ramp → plateau — and a pre-smoothed value blurs exactly that transition.

`tcpi_bytes_received` (which *is* a raw cumulative counter, updated per segment as bytes are enqueued for the application) would let us compute our own received rate with a sampling cadence we control — but it carries the self-measurement ambiguity described above, and gives us essentially the same information as counting bytes from our own `read()` calls.
Hence the burst-probe design: we construct the conditions under which the ambiguity resolves rather than trying to resolve it analytically.

### Sampling cadence: per-`read()`

Samples feed the estimator from inside `peer_on_readable`, immediately after each `read()` returns `n > 0`.
Each sample is `(now, n)` — timestamp and bytes delivered in that read.
No timer, no epoll integration for the estimator itself.

Per-`read()` is finer than per-chunk and makes a real difference on slow links.
On a 5 Mbps / 50 ms RTT link, a single chunk takes ~100 ms to deliver but TCP segments arrive within it every ~2 ms; per-chunk sampling would take ~300 ms to confirm a plateau across three chunks, while per-`read()` sampling confirms the same plateau within ~10 ms inside the first chunk's transmission.
Earlier detection → less overshoot to drain after plateau.
On fast links both cadences are more than adequate, so this is a pure improvement at no complexity cost.

The only thing the estimator doesn't own is the trigger.
`node.c` calls `bdp_sample_bytes(&p->bdp, n, now)` in the read path; `scheduler_bridge.c` reads `bdp_bytes()` / `bdp_state()` when building events for the Python scheduler.
Ring buffer, plateau detector, RTmin min-filter, state transitions, re-probe cadence, and BDP computation all live inside `bdp_estimator.c`.

### Stale estimates

For a peer that has just offered, `TCP_INFO` may have no meaningful RTT (fresh connection) or a stale one (idle connection, no recent payloads).
The policy assigns a small number of probationary chunks to start the feedback loop — enough to get a throughput signal without committing too much work to an unproven peer.
The right number is itself a design question: one is most conservative, but a peer with a high-BDP link would benefit from more to avoid under-utilization during the probe phase.
The probationary chunks serve double duty as potentially useful work and a link quality probe.

## The scheduling policy

The policy is event-driven.
Scheduling decisions are triggered by:

1. **Offer received** — a peer offers this payload. It may be a peer we know well or one we've never exchanged data with. Assign probationary chunks to start the feedback loop.
2. **Chunk delivered** — a peer completed a chunk. Cancel that chunk at any other peer it was also assigned to. Assign the peer more work based on updated estimates.
3. **Stall detected** — TCP_INFO or delivery timing shows degradation on a peer. Deprioritize that peer; potentially reassign its pending chunks.
4. **Periodic re-evaluation** — a timer (e.g., every 100ms) catches slow drifts that don't trigger discrete events.

### Work distribution

The core scheduling function, invoked on each event:
for each peer with capacity (in-flight chunks < pipeline depth target), pull unassigned chunks from the pool and assign them.

Work distribution falls out naturally from the feedback loop: a fast peer has a higher pipeline depth target (larger BDP), drains its in-flight set faster (creating capacity sooner), and therefore gets assigned more chunks over time.
No explicit throughput-proportional weighting is needed — the mechanism is implicit.

### Rebalancing

The natural distribution story assumes unassigned chunks are available when a peer has capacity.
Early in the transfer, especially with few peers, all chunks may be assigned before new peers arrive.
When a new or under-utilized peer has capacity but the unassigned pool is empty, the policy must be able to reclaim chunks from other peers.

A chunk can be reclaimed if it has been assigned but the peer has not yet begun transmitting it (i.e., the REQUEST was sent but the RESPONSE hasn't started arriving, or the assignment is still queued locally).
Reclaiming is cheap — it's just a bookkeeping change, possibly followed by a MSG_CANCEL_CHUNK.
The policy should prefer to reclaim from the peer whose remaining assigned chunks have the longest expected time to delivery — a function of both delivery rate and queue depth at that peer, not bandwidth alone.

### Hedging

Hedging means assigning the same chunk to more than one peer, accepting wasted bandwidth in exchange for reduced tail-latency risk.
Rather than a binary endgame switch, hedging is controlled by a threshold parameter: an **absolute byte size** of remaining undelivered data below which hedging begins.
As remaining work shrinks below the threshold, hedging aggressiveness increases — when 256 KB remains, a chunk might go to two peers; when 64 KB remains, it goes to all peers with capacity.

The threshold is where the operator's bandwidth-vs-latency preference lives.
Setting it to 0 means never hedge (minimize bandwidth waste).
A larger value means earlier and more aggressive hedging (minimize tail latency at the cost of more duplicate work).

Something to revisit later: the right hedging aggressiveness may also depend on the number of available peers and how diverse their link qualities are. More peers = more hedging options = potentially cheaper hedging.

### Stall detection and response

Stall detection must combine TCP-level and application-level signals:

- **TCP-level**: rising `tcpi_lost` or `tcpi_retrans`, RTT spiking above a multiple of the baseline.
- **Application-level**: actual chunk delivery rate (payload goodput). Since component hashes are verified against the manifest, a peer either delivers correct data or is detectably fraudulent (bad hashes → disconnect). The only remaining concern is a peer that delivers correct data but too slowly — which is indistinguishable from a legitimately struggling peer and handled the same way: deprioritize based on observed delivery rate.

On stall detection:
- Stop assigning new chunks to the stalled peer.
- Don't immediately reassign its in-flight chunks — the link may recover from a transient loss burst.
- If the stall persists beyond a timeout (e.g., 2× expected chunk delivery time for that peer), reassign those chunks to other peers.
