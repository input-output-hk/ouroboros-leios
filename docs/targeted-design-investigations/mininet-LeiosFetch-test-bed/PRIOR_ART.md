# Prior Art

**Note on adversarial peers:** some of our peers may be adversarial.
We surveyed adversarial models for P2P systems (BAR Gossip, BAR Fault Tolerance, tit-for-tat analyses) but found that beyond "don't naively trust peers," none offer frameworks relevant to the scheduling challenge specifically.
The provable part (message integrity — invalid data, broken commitments) is handled at the protocol layer via content-addressed hashes.
The scheduling-relevant part (a peer that's slow — deliberately or not) is indistinguishable from an honest struggling peer, and must be handled by the same heuristic observation loop.
See DESIGN.md for how stall detection addresses this.

## Our problem in the abstract

Jobs arrive randomly (average 1 per 20 seconds).
Jobs have unknown size, bounded by a maximum, and are quite granular.
We divide jobs into tasks when they arrive.

We schedule tasks among a set of ~25 workers.
Their performance capabilities are heterogeneous.
Some are adversarial.
Even the honest ones are unreliable due to under-provisioning, overloading (other schedulers also assign load to them), and Internet weather.

Our worker set slowly churns over time.
However, for each job, we can't assign its tasks to a worker until that worker volunteers for that job, which happens at some random delay.

Multiple jobs may be in flight concurrently.
Workers share their finite capacity across all jobs they're working on — both ours and those from other schedulers we can't observe.

Task completion gives us information: each completed task updates our estimate of that worker's current performance.
The scheduler is learning online, not just dispatching.

**Objective:** balance how long it takes to complete a job (all of its tasks) against how much excess load we put onto our workers.

## Related work

### Speculative execution / hedged requests

Dean & Barroso, "The Tail at Scale" (2013).
Google's approach to tail latency: send redundant requests to multiple servers, take the first response, cancel the rest.
The key insight — redundancy is cheap when you cancel promptly — maps directly to our chunk-level cancel mechanism.
Their "tied requests" variant, where servers cancel each other's duplicates, is analogous to our MSG_CANCEL_CHUNK.
Key difference: Google controls both sides and has homogeneous, well-provisioned servers.
We have heterogeneous, unreliable, potentially adversarial workers whose capacity we share with unknown other schedulers.

### Multi-armed bandit / explore-exploit

Our probationary task assignment is the exploration phase; scaling up pipeline depth to proven workers is exploitation.
The tension: spend too long exploring and you waste time on slow workers; exploit too aggressively and you miss a fast worker that arrived late.
The difference from textbook bandits is that our arms' reward distributions are nonstationary (workers degrade and recover) and we get side information (TCP_INFO) rather than only observing rewards.

### Power of two choices

Mitzenmacher, "The Power of Two Choices in Randomized Load Balancing" (2001).
Instead of assigning a task to the globally "best" worker or a random one, probe two and pick the less loaded.
A cheap way to get near-optimal load balance without global coordination.
Relevant to our rebalancing: when deciding who to reclaim from, comparing two candidates is nearly as good as finding the true worst.
Key differences: their supermarket model assumes homogeneous servers, atomic jobs, and observable queue lengths.
Our workers are heterogeneous, our jobs are divisible into many tasks, and we can only partially observe worker load (TCP_INFO estimates, not ground truth — other schedulers' load is invisible to us).

### Work stealing

Blumofe & Leiserson, "Scheduling Multithreaded Computations by Work Stealing" (1999), as implemented in Cilk.
Idle workers steal tasks from busy ones.
Our rebalancing is the inverse: we (the scheduler) reclaim tasks on behalf of under-utilized workers.
The key parallel is that stealing is reactive to observed imbalance rather than planned upfront.
Key difference: work stealing assumes a shared-memory environment where steal cost is uniform and low.
Our "steals" cross the network — reclaiming a chunk costs a MSG_CANCEL_CHUNK round-trip to the donor and a new MSG_REQUEST to the recipient, both with variable latency.

### Weighted fair queuing / proportional share scheduling

Our natural work distribution — faster workers drain their pipelines sooner, get more work — is essentially a throughput-proportional share scheduler, achieved implicitly through the feedback loop rather than explicitly computed weights.
Key difference: traditional WFQ/proportional-share schedulers know the weights upfront (or derive them from policy).
We discover them at runtime through observation, and they change continuously.

### Straggler mitigation in MapReduce

Dean & Ghemawat, "MapReduce: Simplified Data Processing on Large Clusters" (2004).
Zaharia et al., "Improving MapReduce Performance in Heterogeneous Environments" (LATE scheduler, 2008).
Large parallel jobs are bottlenecked by the slowest task.
Speculative re-execution of slow tasks is the standard fix.
Zaharia's insight: speculate based on estimated remaining time, not just elapsed time.
Our rebalancing follows this: reclaim from the peer with the longest expected delivery time.
Key difference: MapReduce has a central scheduler with global visibility and a fixed worker pool.
Our workers volunteer asynchronously and may disappear, and we have no visibility into what other load they carry.

### Adaptive load balancing with health checks

Production load balancers (Envoy, nginx, HAProxy) use active and passive health signals to route traffic away from degraded backends.
Our TCP_INFO polling plus payload goodput monitoring is the same pattern: passive observation supplemented by derived health signals, with circuit-breaker behavior on stall detection.
Key difference: load balancers choose among backends for each new request independently.
We maintain ongoing relationships with workers across many tasks within a job — a "stalled" worker may have several of our chunks in flight that need to be reclaimed, not just one request to retry elsewhere.

### Erasure codes

A different angle entirely: encode the payload so that any k-of-n coded chunks suffice to reconstruct the original data.
This eliminates the "tail task" problem — you don't care *which* worker delivers, just that *enough* total data arrives.
Scheduling reduces to "get data from anyone as fast as possible" with no chunk-identity tracking.

Several families exist:
- **Fixed-rate** (n chosen at encoding time):
  - **Reed-Solomon:** optimal (any k of n suffice) but O(n²) encoding/decoding, practical only for moderate n.
  - **LDPC (Low-Density Parity-Check):** near-optimal recovery with linear-time encoding/decoding. Used in 5G, DVB-S2, etc.
  - **Raptor codes:** near-optimal recovery with very fast linear-time encoding. Used in 3GPP MBMS (mobile broadcast).
- **Rateless / fountain** (encoder can generate an unbounded stream of coded symbols):
  - **LT codes:** the original fountain code. Simple but needs ~5% overhead above k symbols for decoding.
  - **RaptorQ:** practical refinement, near-zero overhead, fast encoding and decoding.

The distinction between fixed-rate and rateless matters here.
With fixed-rate codes, the n coded symbols are deterministic — if all peers hold the same set, you're back to our exact scheduling problem (specific symbols, duplicate waste, cancellation needed).
Avoiding duplicates requires coordinated distribution of different symbol subsets to different peers, which reintroduces coordination at a different layer.
With fountain/rateless codes, each peer independently generates symbols using random coefficients, so duplicates are astronomically unlikely.
This is the only variant that truly eliminates the coordination problem — every symbol from every peer is useful.

However, erasure codes don't eliminate scheduling entirely.
You still need to distribute requests across peers to minimize time-to-k: pipeline depth management, stall detection, and throughput-proportional rebalancing all remain.
What disappears is hedging/cancellation — there's no duplicate work to cancel.
Massoulié & Vojnovic ("Coupon Replication Systems", IEEE/ACM ToN 2008) analyzed optimal piece distribution and showed that coding-based approaches can beat rarest-first for completion time, providing theoretical grounding for this claim.

A peer with the full payload could act as a fountain encoder, generating unique coded symbols on the fly for each requester — RaptorQ encoding is O(k) per symbol, fast enough to run at line rate.
This is a compelling alternative architecture that eliminates our hardest scheduling problem (hedging/cancellation) while preserving the pipeline depth and rebalancing problems.

RFC 3453 ("The Use of Forward Error Correction in Reliable Multicast", 2003) lays out the progression from Reed-Solomon through Tornado codes to LT codes and makes the case for FEC in multicast.
It notes that rateless codes enable multi-sender scenarios (Section 2.4) but doesn't develop receiver-side scheduling across heterogeneous sources.

Key difference: our components have content-addressed hashes that consumers verify — erasure-coded symbols aren't individually verifiable against the manifest without additional commitment structure.
This is at least a hurdle but not obviously a dead end (Claude pins homomorphic hashing or polynomial commitment schemes as potential tools, but I haven't pressed that at all yet).
Worth revisiting as a future direction.

### Avalanche (network coding in P2P)

Gkantsidis & Rodriguez, "Avalanche: File Swarming with Network Coding" (INFOCOM 2005, Microsoft Research).
Applies random linear network coding to P2P file distribution.
The key design point: every peer **re-encodes** — it generates fresh random linear combinations over a finite field from all coded blocks it has received, rather than forwarding received symbols verbatim.
This means every peer is a source of novel coded information at every hop, not just the originator.

Scheduling is receiver-driven pull: peers advertise which "generations" (file segments) they have innovative (linearly independent) information for; the receiver requests coded blocks for generations where it still needs more independent symbols.
Any coded block from any peer is (with high probability) useful, so there are no "rare pieces" and no coupon-collector tail.
The paper showed 2-3× faster distribution completion than BitTorrent, with the improvement most pronounced in the tail — the slowest peers finish much faster.

Avalanche was never deployed.
Two problems killed it:
- **Pollution attacks.** A malicious peer can inject a single invalid coded block, which gets re-encoded and propagated, corrupting the entire generation across the swarm. The original paper acknowledged but did not solve this. Follow-up work (Boneh, Freeman, Katz, Waters, "Signatures for Network Coding", 2009) proposed homomorphic signatures for per-symbol verification, but with significant computational overhead.
- **Computational cost.** Finite-field arithmetic for re-encoding at every peer was expensive at the time.

Key differences from our setting:
Re-encoding at every hop amplifies the pollution attack surface — one bad symbol propagates.
Source-only coding (peers forward but don't re-encode) would avoid this but loses the "every peer generates novel information" property that eliminates rare pieces.
Our content-addressed hash model has the same tension: per-symbol integrity verification is what makes pollution attacks detectable, and it's exactly what network coding breaks.

Sundararajan et al. ("Network Coding Meets TCP", 2011) later explored the practical transport-layer challenges of integrating network coding with TCP, addressing issues like in-order delivery and congestion control that Avalanche left open.

Avalanche's scheduling insight is nonetheless valuable: in a network-coded system, the receiver's scheduling problem reduces to "maximize total innovative symbol throughput across peers" — pipeline depth and throughput-proportional distribution still matter, but hedging and cancellation disappear entirely.

## P2P-specific prior art

### BitTorrent

BitTorrent divides a file into **pieces** (typically 256 KB–4 MB), each with a SHA-1 hash for integrity verification.
Pieces are further divided into **blocks** (16 KiB), which are the unit of network transfer — a single REQUEST/PIECE message pair carries one block.
A piece can only be verified and shared with other peers once all of its blocks have been received.

BitTorrent uses three distinct piece selection modes.
A client that is still downloading (a "leecher", as opposed to a "seeder" that has the complete file) selects its first piece at random to get *something* complete quickly, since rare pieces may only be available from slow peers.
After the first piece, the client switches to rarest-first: request the piece available from the fewest peers in the swarm, which replicates rare pieces quickly and improves swarm health.
Near the end of a download, the client enters endgame mode: once every remaining piece has at least one pending request, the client sends duplicate requests for all remaining blocks to every peer that has them, and sends CANCEL messages when a block arrives from any peer.

libtorrent (the engine behind qBittorrent, Deluge, and others) dynamically computes per-peer pipeline depth as `bandwidth × RTT / block_size` (where block size is 16 KiB), capped at roughly 500 outstanding requests.
This is essentially the same BDP-based approach we use with `TCP_INFO`.
Once a single block of a piece arrives, libtorrent applies "strict priority" to that piece — all remaining blocks are requested before starting new pieces — to minimize the number of partially-complete pieces.
The client also avoids assigning rare pieces to slow peers, since a slow peer holding the only copy of a rare piece would bottleneck the entire swarm.

BitTorrent optimizes for throughput and swarm health, not per-file completion latency.
Rarest-first maximizes piece diversity across the swarm; endgame mode helps tail latency but is a brute-force mechanism (duplicate everything remaining).
There is no continuous rebalancing or throughput-proportional work distribution mid-transfer.
Key references: Cohen (2003), Legout et al. "Rarest First and Choke Algorithms Are Enough" (IMC 2006).

### IPFS Bitswap

Bitswap uses a "session" abstraction to group related block requests (e.g., all blocks needed to resolve a DAG).
Each session maintains a set of peers that have previously responded with wanted blocks and preferentially routes future requests to them.

The protocol evolved significantly across versions.
Bitswap 1.0 broadcast every want to all peers, causing massive duplicate traffic (the "Bitswap tax").
Bitswap 1.1 introduced a WANT-HAVE / WANT-BLOCK split: nodes first send cheap WANT-HAVE messages to discover who has a block, then send WANT-BLOCK to a single peer, dramatically reducing duplicate bytes.
Bitswap 1.2 added session-level peer scoring based on response history (weighted random selection, not formal BDP estimation), request splitting across peers in parallel, and improved CANCEL messages when a block arrives.

Stall handling is timeout-based: if a peer does not respond within a deadline (10-30 seconds depending on version), the session marks it unresponsive and reassigns the want to another peer.
There is no speculative redundant requesting — it is strictly single-assignment with timeout failover.
This means tail latency is bounded below by the timeout value, which is a known weakness.
Key reference: Daniel et al. "Accelerating Content Routing with Bitswap" (IFIP Networking 2021).

### P2P live streaming

CoolStreaming (Zhang et al., INFOCOM 2005) and LiveSky (Yin et al., INFOCOM 2009) use pull-based mesh streaming with deadline-aware chunk scheduling.
Kumar et al. (2007) analyzed "random-useful" scheduling — where a node requests a randomly chosen chunk that the neighbor has and the node lacks — and showed that while it is near-optimal under homogeneous conditions, it degrades significantly under heterogeneity because it doesn't account for which peers can deliver faster.
Magharei, Rejaie, Guo (2009) directly studied how bandwidth heterogeneity affects chunk delivery latency in mesh-based streaming.

Of all the prior art, P2P streaming is the closest match to our *environment*: pull-based mesh, heterogeneous unreliable peers, chunk-level scheduling decisions, no central control.
Tail at Scale is the closest match to our *mechanism*: hedged requests, cancel on first completion, latency as the objective.
Our problem lives at the intersection.

**Similarities with streaming:** the underlying machinery is the same — decide which chunks to request from which peers in a heterogeneous pull-based mesh.
Their urgency-weighted scheduling, buffer map exchange, and degradation analysis under heterogeneity all transfer to our setting.
(Their CDN fallback mechanism does not — our data is only available via our protocol, with no reliable out-of-band source to fall back to. We can only "fallback" to more aggressive redundancy in requests.)
Sequential ordering is not crucial for us but would be a nice-to-have, so their deadline-aware techniques aren't entirely irrelevant.

**What streaming has that we lack:**

- A clean urgency signal.
  Playback buffer depth tells a streaming scheduler exactly how worried to be at any moment — 10 seconds of buffer means be selective, 0.5 seconds means get aggressive.
  The consumption rate is constant and known, so buffer depth is a reliable predictor of future trouble.
  We have something analogous but noisier.
  Each payload has a verifiable timestamp and the network has a general target (~14 seconds for the last peer to complete).
  Combining time remaining (`target - elapsed`) with local progress (remaining chunks) gives a "required rate" signal: how fast we need to go to finish in time.
  But this signal is less trustworthy than streaming's for several reasons: adversarial nodes may backdate timestamps (making urgency look artificially high), our payload arrival rate is random (concurrent payloads compete for peer bandwidth in unpredictable bursts), and the "required rate" is an estimate built on estimates (per-peer throughput, capacity split across concurrent jobs, unknown future arrivals).
  Streaming reads urgency off a buffer counter; we compute it from a stack of noisy approximations.

- Stable source topology.
  In streaming, the same source broadcasts continuously and peers have consistent relative positions in the mesh.
  Per-peer performance rankings are relatively stable across chunks of the same stream, so learning from recent history is reliable.
  In our system, each payload originates at a different point in the network.
  The propagation wavefront hits our peers in a different order for each job, so a peer that was the fastest source for the last payload might be the slowest for the next one.
  Cross-job learning about peer quality is less valuable than it appears.
  Historical stats are useful for judging whether a peer is generally worthwhile (good link, responsive, not adversarial), but only loosely informative about how much they can help with any specific payload — that depends on where the payload originated relative to them, which resets every time.
  This is why our probationary chunk mechanism matters for every job, not just the first.

## What we should co-opt

- **libtorrent's dynamic pipeline depth** — validates our BDP/chunk_size approach.
- **BitTorrent's endgame trigger** — activate hedging when the unassigned pool is empty (all remaining chunks have at least one pending request). Cleaner than a pure byte threshold.
- **Bitswap's WANT-HAVE / WANT-BLOCK split** — we already have this in OFFER / REQUEST.


## What nobody does that we need

- **Continuous rebalancing mid-transfer.** BitTorrent avoids rare-piece-on-slow-peer but doesn't reclaim. Bitswap waits for a full timeout. Neither adapts in real-time based on observed throughput.
- **Parameterized hedging.** Others either never hedge (Bitswap) or always hedge at endgame (BitTorrent). We need a tunable ramp controlled by operator preference and/or in-bind governance-determined protcol parameter.
- **Latency as a first-class objective** rather than throughput (BitTorrent), content availability (IPFS), or playback continuity (streaming).
- **Per-job re-exploration.** In all the prior art, per-peer performance is relatively stable across units of work. Our wavefront reordering (each payload originates at a different network location) means peer rankings reset with each new payload, requiring fresh probing every time.
- **Hedging calibration from a noisy urgency signal.** We have an urgency signal (payload timestamp + network target deadline + local progress), but it's less trustworthy than streaming's buffer depth: adversarial timestamps can inflate urgency, random payload arrival creates unpredictable contention across concurrent jobs, and the "required rate" is an estimate built on estimates. Streaming reads urgency off a counter; we compute it from a stack of noisy approximations.

## Strongest analogies for communicating the design

No single reference captures our full problem.
**Tail at Scale** matches our mechanism (hedged requests, cancel on completion, latency as objective) but assumes a controlled environment.
**P2P streaming** matches our environment (pull-based mesh, heterogeneous unreliable peers, chunk-level scheduling) but has stable propagation structure and a continuous urgency signal we lack.
Our problem lives at the intersection.

Specific analogies:
- **Tail at Scale** for the hedging story.
- **P2P streaming** for the "scheduling chunks across heterogeneous peers in a mesh" story.
- **MapReduce straggler mitigation** for the rebalancing story.
- **Multi-armed bandit** for the exploration/exploitation framing.
- **BitTorrent endgame mode** for the "duplicate remaining chunks" mechanism (but ours is parameterized, not all-or-nothing).
- **libtorrent pipeline depth** for the BDP-based request windowing.
