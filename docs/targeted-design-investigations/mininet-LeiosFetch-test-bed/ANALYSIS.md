# Analysis: fetch strategy trade-offs

A node pulling a large payload from multiple peers has to decide *what to request from whom and when*.
The central tension is between **wasted bandwidth** (duplicate in-flight requests) and **pessimized tail latency** (committing too early to a peer that turns out slow).
This document walks through the extremes of that spectrum and then shows why a BDP-aware middle policy wins on both axes against unbounded hedging and on one axis against the minimal policy.

## The spectrum: OnePeer and FullHedge

To bracket the policy space, we implement two extremes that make no attempt to estimate peer quality.

**OnePeerScheduler** (`OnePeerScheduler.py`).
As soon as both the manifest and one offer are available for a payload, request every chunk from the *first* offering peer and never assign to any other peer.
No hedging, no probing, no rebalancing, no cancellation — if the chosen peer is slow, you wait.

**FullHedgeScheduler** (`FullHedgeScheduler.py`).
As soon as a manifest is available and the peer has offered, request every chunk that we don't already have from this peer.
When any chunk lands from one peer, cancel the duplicate in-flight requests at the other peers.
Permutes request order per peer so different peers transmit different chunks first, and then has cancellation race the wire for anything already committed to a kernel send buffer.

These two represent opposite endpoints: minimal bandwidth usage with no tail-latency protection, and maximal duplication with as much protection as possible.

## Demonstration: 8-1 coinjection

The `topo-8-1` topology (see `topology.png`) has 8 source nodes, each with a distinct capacity/delay/loss link to a single Sink.
The `schedule-12MB-11-20s-apart-coinj8` schedule artificially injects each 12 MB payload at all 8 source simultaneously; the Sink can start pulling from all 8 as soon as they offer.

Two payloads, one run per scheduler:

| payload | OnePeer | FullHedge | Fetch |
|---|---|---|---|
| ce4b81c… | 10118 ms | 3122 ms | **2297 ms** |
| c50beee… | 10181 ms | 3038 ms | **2047 ms** |

| scheduler | total wire MB |
|---|---|
| OnePeer | **52.7** |
| Fetch | 59.9 |
| FullHedge | 96.9 |

### OnePeer

Latency: ~10 s per payload, corresponding almost exactly to serving the full payload from whichever single peer answered first.
With co-injected offers, "first to offer" is essentially the first TCP handshake to win the race — a random peer, not necessarily the fastest one.
If that peer turns out to be the 3 Mbit link, you spend the full 32 s a 12 MB payload takes at 3 Mbit, roughly.

Bandwidth: ~53 MB, the theoretical floor (12 MB × 2 payloads × ~2 one-way counted-twice-in-pcap, plus protocol overhead).
OnePeer never duplicates, so every byte on the wire is useful — that's the entire win of the minimal policy.

### FullHedge

Latency: ~3.1 s, bounded now by the *fastest* peer's link time (roughly 12 MB / 12 Mbit ≈ 8 s… minus what the peer shuffles contribute in early per-peer chunk diversity).
The tail-latency protection is real: a slow or lossy peer no longer holds the Sink back because seven other peers are delivering the same chunks.

Bandwidth: ~97 MB, ~2× the OnePeer floor.
Cancellation recovers most of the duplicates, but whatever has been committed to a source node's kernel send buffer between request and cancel is unrecoverable.
The cost is paid in aggregate by slow peers whose chunks mostly arrive after faster peers have already delivered them.

### Fetch

Latency: ~2.2 s — *better than FullHedge* despite hedging far less aggressively.
Bandwidth: ~60 MB, close to the OnePeer floor.

Fetch isn't Pareto-dominant: OnePeer still uses fewer bytes on the wire.
But it is sweetspot-proximal.
Given how cheap the marginal bandwidth is relative to OnePeer's 5× latency penalty, and how much bandwidth FullHedge spends to end up slower, Fetch's point is the one an operator would rationally choose.

## Caveats

**The BDP estimator is stubbed with an oracle.**
Fetch's behaviour below depends on knowing each peer's BDP and minimum RTT.
In this simulator we stub that estimate with an oracle that reads the values directly from the topology config — see `scheduler_bridge.c`.
So the numbers above are a best case for Fetch: they answer the question *"given that you can estimate BDP, what policy should you run?"* rather than *"can you estimate BDP well enough to run this policy?"*.
The `bdp_demo/` directory shows why the real problem — receiver-side BDP measurement on a bursty TCP stream — is non-trivial, and DESIGN.md describes the probe-based approach we use when the oracle is replaced.

Also: the 8-1 topology stresses the tail scenario specifically.
On a topology where all peers are similar and the tail doesn't matter, FullHedge's tail protection is wasted bandwidth and OnePeer is competitive.
On a topology where peer quality varies wildly mid-fetch, a more aggressive rebalance policy might beat Fetch's conservative one.

## What makes Fetch win

Fetch's key advantage is that it **estimates each peer's BDP** early in the exchange and uses that to size per-peer in-flight work.

When a peer first offers, Fetch probes it with a short burst of chunk requests big enough to fill the pipe and drive TCP past slow-start.
The C-side bdp_estimator watches the arrival rate and signals `BdpEstimated` once it plateaus — at which point Fetch knows, for that specific peer, how many bytes of concurrent in-flight work keeps the link saturated without wasting capacity.

With that per-peer BDP in hand, three things follow:

1. **Pipeline depth is calibrated, not guessed.**
   Fast peers get proportionally more work in flight, slow peers less.
   OnePeer never calibrates (it uses one peer); FullHedge doesn't need to (it fills every peer's queue regardless).

2. **Rebalancing has a throughput signal to act on.**
   If a peer's BDP/RTT product shrinks mid-fetch — a loss burst, bufferbloat spike, a slower peer than it first appeared — Fetch can cancel its chunks and reassign them to a peer whose estimate shows more headroom.
   The BDP estimate turns "which peers are fast *right now*" from a guess into an observable.

3. **Hedging is thresholded, not unbounded.**
   FullHedge hedges every chunk to every peer from the start; OnePeer never hedges.
   Fetch hedges only when the remaining payload is small enough (below a configured byte threshold) that duplicating the last few chunks is cheap insurance against the tail getting stuck behind a slow peer.
   This only works because Fetch already has throughput estimates to tell it *which* remaining peers to hedge to.

The BDP-aware policy uses OnePeer's bandwidth-efficient pattern for the bulk of the payload and adds FullHedge's tail protection only where it pays.
Without the BDP signal, neither of those moves is possible — you either commit everything to one peer with no tail recourse, or duplicate everything everywhere and sort it out with cancellation.

## Adversarial resilience

Because the components' hashes are part of the pre-distributed manifest, any outright lie about payload content is caught on the first bytes.
The remaining attack surface is the *fetch decision*: a peer who advertises a fast link (or delivers quickly during the initial probe) and then stalls — a classic slow-loris / tarpit.
The damage such a peer can inflict is exactly how much the scheduler is willing to forgive an honest-but-struggling peer before routing work elsewhere.

**FullHedge**: unaffected.
Every chunk is already being fetched from every other peer; a tarpit simply contributes zero useful data and gets its requests cancelled as the rest of the swarm delivers.

**OnePeer**: fails catastrophically.
If the tarpit happens to be the first to offer, the entire payload is stranded until the tarpit eventually decides to respond (or the socket times out).
No detection, no recovery.

**Fetch**: bounded but not free, and the bound compounds against multiple colluding tarpits.
The tarpit gets one chance to lie during the BDP probe, which makes Fetch treat it as a high-capacity peer and assign it a deep pipeline of chunks.
When the chunks don't arrive by their per-chunk stall deadline (STALL_TIMEOUT_MULTIPLIER × estimated delivery time from the oracle BDP), Fetch snubs the peer, cancels its in-flight chunks, and reassigns them to peers with remaining capacity.
The cost of a single tarpit is roughly one BDP-worth of work wasted on it plus one snub-to-reassign cycle of added tail latency — measured in hundreds of ms on the 8-1 topology, not in the seconds-per-payload territory where OnePeer lives.
If the reassignment happens to land on *another* tarpit the cost repeats, snub by snub, until honest peers pick up the chunks — so a swarm with N of M peers adversarial pays roughly N such cycles in the worst case.
The tarpit's leverage is capped by how generously we set the stall threshold.
That threshold is the knob that trades adversarial resilience against tolerance of honest-but-noisy peers.
