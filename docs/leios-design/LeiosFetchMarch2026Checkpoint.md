# Introduction

This report summarizes the high-level challenges that the LeiosFetch decision logic faces.
It also proposes an outline of the high-level rules that would navigate those challenges.

This particular document has two concrete purposes.

- Snapshot the high-level design of the LeiosFetch decision logic as of the end of 2026 March.
- Catalyze critique and contributions from teammates and community members interested in the architecture.

# High-Level Challenges

The following list provides a terse but somewhat self-contained description of each challenge.
Future writing will elaborate on each and their interactions.
It's useful for this single document to collate their essential descriptions since LeiosFetch lies at their intersection.

- **Challenge**: the stakes are high, even for rare events (a.k.a. "in the tail").
  Unanticipated latency of EB diffusion risks increasing the latency of Praos messages.
  If a Praos block contains a certificate for an EB, a node cannot fully select that Praos block before it receives that EB.
  Thus, the absence of an EB could increase Δ_Praos (a.k.a. Δ_RB), thereby degrading Praos security.
  This is the most important risk for Leios, since Praos is the foundation of not only the Leios security argument but the Cardano security argument.
    - **Constraint**: The worst-case cannot be ignored.

- **Challenge**: multiple hops.
  The EB diffusion in question starts at the EB producer and ends at "every" other honest node (analyses can disqualify honest nodes if they're latency outliers and the honest stake ratio is high enough to afford their loss).
  Previous work has reported that the shortest path usually involves ≤ ~6 hops.
  Some extra complexity can be added to pipelining those hops, but it won't be perfect.
  LeiosFetch only manages the communication along one hop and the next (i.e. both sides of a single node), with the performance constraint tight enough that a composition of ~6 hops still has low enough end-to-end latency (≤ ~14 seconds for a healthy EB, accoding to CIP-0164).
    - **Constraint**: Per-hop latency needs to be quite short, ~2 to ~3 seconds.

- **Challenge**: peers are permissionless.
  Peers are identifiable only by their current IP address and port.
  Some peers can be sampled from the stake pools' registration data, but not all peers---even upstream peers---are acquired that way.
  (TODO is that fact a hard constraint on the design?)
    - **Constraint**: There are too many potential peer names to definitely keep a significant history of performance/quality profiles.

- **Challenge**: unpredictable latency and bandwidth, per peer.
  A peer's past performance does not necessarily correlate with its future performance.
  Even for completely trustworthy peers, the particular traffic route is dynamic and not necessarily reliable, since Cardano operates over the public Internet.
  Moreover, not at all peers are trustworthy, so even if the physical performance hasn't changed, any peer could suddenly choose to respond much more slowly or not at all.
  Timeouts limit the affect of so-called _low-and-slow_ attacks, but two principal difficulties remain.
    - Timeout false alarms are harmful to the network topology and hence also delay EB diffusion, so the thresholds cannot be arbitrarily tight.
    - It's not obvious what the tolerable performance lower bounds are nor how they should vary across time and/or peers.
    - **Constraint**: LeiosFetch must quickly react to changes in peer behavior.

- **Challenge**: intercontinental peers are important.
  Despite intercontinental peers inherently exhibiting poor latency, they drastically improve the diffusion of EBs through the global Cardano network when well-utilized.
  Thus, There is no one-dimensional metric that would be sufficient for peer performance: a variety of peers is desired.
    - This makes timeouts even more complicated to enforce.
    - An intercontinental peer is best utilized by saturating its high Bandwidth-Delay Product (BDP), which requires proportional memory.
    - **Constraint**: LeiosFetch should treat peers heterogenously (e.g. different BDPs).

- **Challenge**: unpredictable patterns for short-term Leios load, network-wide.
  The arrival rate of valid Linear Leios traffic is constrained by the Praos leader schedule.
  However, the leader schedule is random, so several EBs can arise in a short-time frame.
  It won't be frequent, but it is possible and so must be accommodated (or at least recoverable).
  The tolerable error probabilities are so low that something like 30 EBs arising within 15 seconds is a plausible concern (a.k.a. _protocol storm_).
    - **Constraint**: Even honest behavior can overwhelm the nodes' resources in the worst-case.

- **Challenge**: protocol bursts.
  The adversary can arrange for thousands of old EBs to diffuse late, such that they're all diffusing (or at least eligible for diffusion) at the same time.
  The key idea of FreshestFirst prioritization is to diffuse these old EBs only while no younger EB is diffusing.
  However, sending network requests and handling them involes systems with inertia, so that simple rule is not trivial to implement.
    - **Constraint**: LeiosFetch must not over-commit resources to _potentially_ low-priority data.
  
- **Challenge**: unpredictable patterns for short-term Leios load, per peer.
  It's unclear which upstream peers will be the first to serve the next EB and which downstream peers will need to request it.
    - **Constraint**: There are no straight-forward and reliable heuristics for LeiosFetch to leverage.

- **Challenge**: scarce resources per upstream peer.
  The Leios node has a limited amount of CPU, RAM, and local networking resources.
  A typical node's connectivity involves ~25 upstream peers.
  LeiosFetch must prevent adversarial peers---who cannot be identified a priori---from consuming too much more than their fair share of those resources.
    - **Constraint**: LeiosFetch cannot simply request every EB offered.

- **Challenge**: scarce resources per downstream peer.
  The Leios node has a limited amount of CPU, RAM, and local networking resources.
  Popular nodes will serve > 100 downstream peers at once, so the server-side logic's must utilize resources frugally.
  LeiosFetch must prevent adversarial peers---who cannot be identified a priori---from consuming too much more than their fair share of those resources.
    - **Constraint**: LeiosFetch cannot simply serve every EB it offers.

- **Challenge**: EBs are large enough that their resource usage does not trivially scale.
  CIP-0164 bounds the size of an EB at ≤ 12.512 MB; just 80 maximal EBs would already exceed 1 GB.
  For example, if a popular node were to relay one maximal EB to every downstream peer, that alone would consume > 1.2512 GB of egress bandwidth.
    - **Constraint**: LeiosFetch cannot simply request every EB from every peer that offers it.

- **Challenge**: EBs are granular enough that resource usage of bookkeeping does not trivially scale.
  A single EB could contain ~15000 individual transactions (that's 512 kB ÷ 34 B/tx, where each transaction is referenced by the pair of 32 B hash and 2 B size).
  Even with a typical leader schedule, the node could at any given time be obligated to acquire and provide any of ~30 million distinct transactions.
  With a worst-case leader schedule, the universe of volatile transactions would be ≤ ~150 million transactions.
    - **Constraint**: LeiosFetch itself---separate from per-peer buffers, etc.---will need to reserve significant portions of RAM (estimate of at least ~1 GB).

- **Challenge**: mempool fragmentation attacks.
  An adversary could significantly reduce the extent to which the contents of the global mempools agree.
  For example, the mempools of nodes in North America and the mempools of nodes in Europe typically contain very similar sets of transactions.
  Existing mechanisms prevent this even if different parties were flooding the US and Europe with separate transaction streams: the direct connections between US and European nodes would get their fair chance to add the next transaction to each mempool.
  However, if an adversary were to open a disproprotionate number of connections, they could overwhelm that fairness mechanism and thereby drastically reduce the amount of overlap between the US and Europe mempools.
  Linear Leios is intended to work even under this circumstance, though some reduced Quality of Service is acceptable---a proportional degradation is tolerable because botnets are expensive to sustain.
  The key mechanism is the TxCache: when the first EB to diffuse from one continent to the other during the fragmentation attack will be too slow to succeed, its diffusion will warm up the TxCache such that the second EB diffusing in that same direction will require much less bandwidth.
  This process repeats each time an EB diffusing in that same direction succeeds, until the mempool fragmentation ends.
    - **Constraint**: LeiosFetch will need to maintain and leverage the TxCache.

# Prior Art: Praos

The Praos protocol (esp. BlockFetch) faces many of the same challenges, but not all.
One key distinction is a matter of scaling.
- The size ratio of a maximal Praos block to a maximal EB is 1 to 139.
  For example, a TxCache is irrelevant for Praos because Praos blocks are small enough to diffuse well unassisted even during a mempool fragmentation attack.
- Moreover, the diffusion of a Praos block fundamentally only requires a single ≤ ~90 kB all-or-nothing blob rather than the careful subset selection from ≤ ~15000 variably-sized parts.
Another key distinction is that only the Praos blocks on the best Praos chain need to be diffused, whereas Linear Leios requires all EBs to be diffused so that they'll be available if a subsequent Praos switch requires them.

Ultimately, Praos is lightweight enough to be less challenging.
As a result, a greater fraction of a node's peers will each be performant enough to diffuse a Praos block within the required latency.
The difference is unsurpising, since Leios so drastically increases throughput.

# Prior Art: The Tail At Scale

"[The Tail At Scale](https://research.google/pubs/the-tail-at-scale/)" by Jeffrey Dean and Luiz André Barroso (2013) discusses a similar goal: improving worst-case latencies among a large network of machines.
There are two key differences.
- Their network of concern is operated by the protocol designers.
  That is qualitatively different scenario than the "unpredictable latency and bandwidth", "peers are permissionless", "multiple hops", and "unpredictable patterns for short-term Leios load" challenges, etc.
- Moreover, the stakes are lower.
  The cost of inflated tail latency within a fleet is proportional to its extent and duration; that could be costly, but not existential.
  The cost of Leios accidentally delaying some Praos blocks is instead whether or not the Cardano security argument has an unmitigated gap.

Even so, this prior art is an appropriate place to anchor the LeiosFetch implementation's design.
It describes four ideas that could be leveraged by the LeiosFetch logic.
- _Hedge requests_ are intentionally redundant requests, sent because---even among a centralized fleet---it's unknown which peer will be first to successfully reply.
  The extra M - 1 copies of bandwidth is worthwhile overhead, incurred to reduce the probability of a problematically delayed response from P to Q, where P is a hopeful choice among a set of probabilities p_i and Q is instead the product Π p_i for i ∈ some M-sized subset of {1..N}.
- _Tied requests_ are a mechanism so that not all of the M requests will be processed.
  Whichever request is processed soon enough might occur so much faster that some of the other requests could be cancelled.
  The original requests themselves cannot be unsent, but a "cancel-if-you-haven't-already-started" message might arrive in time to relieve some load from an overloaded peer.
- A _shadow request_ is additional hedge request beyond the M requests.
  It is sent to a peer that is currently on _probation_/being _snubbed_ because its past performance fell below acceptable tolerances.
  If their performance has since increased and their response is now competitive, their probation can be lifted.

Shadow requests seem the least likely mechanism for LeiosFetch to adopt, since Cardano nodes typically simply disconnect when a peer performs below tolerances (e.g. times out).
Perhaps an intermediate probation stage could be useful, though.

Tied requests cannot be implemented as in the paper.
There, the concrete suggestion was two-fold.
- Upstream peers communicate with each other in order to cancel requests, since that way the cancellation can be sent as soon as the first response is _sent_ rather than _received_.
- Clients should send hedge requests only after a delay of "two times the average network message delay (1ms or less in modern data-center networks)".
  That way, 95% of the time, the first server to succeed can send a cancellation before the other servers receive their copy of the client request.
The recommendation of the average ping obviously conflicts with at least the "unpredictable latency and bandwidth" and "intercontinental peers are important" challenges.
That design also assumes that all the servers (i.e. upstream peers) are interconnected, which is not the case in Cardano.

Ultimately, hedge requests and some best-effort form of tied requests (i.e. clients send cancel-if-you-haven't-already-started) could be implemented in LeiosFetch (in BlockFetch/TxSubmission/etc. too, if deemed worthwhile).

# Prior Art: other blockchains

TODO find people with greater expertise---I'm a comparatively sheltered Ouroboros/Cardano expert

- Major difference: Bitcoin has a much longer duration between blocks and payloads < 1 MB.

- Major difference: Ethereum does have Proto-Danksharding, but those payloads are < 1 MB.
  I did not find detailed material on the higher-throughput future [Danksharding](https://ethereum.org/roadmap/danksharding) (without the Proto- prefix); it seems comparable to so-called Full Leios.

- Solana's _Turbine_ does have a resemblance.
  For example, erasure coding is a more sophisticated evolution of hedge requests.
  https://solana.com/news/turbine---solana-s-block-propagation-protocol-solves-the-scalability-trilemma
  Major difference: The tree structure is a crucial element, and the existing Cardano p2p logic is not obviously compatible with that; e.g. that article mentions ~2 hops instead of our ~6.
  Major difference: The Solana objective includes much higher sustained traffic, so hopefully Linear Leios doesn't require as much complexity.
  Major difference: They're separately compensating for UDP issues instead of accepting TCP's limitations.

# Terminology

The usual English terms---even typical jargon---for these topics are not very precise.
This brief section pins down preferred terminology, for the sake of the reader.

At the scale of a single node:

- An EbBody/EbClosure is _offered_ if a MsgLeiosBlockOffer/MsgLeiosBlockTxsOffer for that EB has already been received from at least one of the current upstream peers.
    - If all the peers that have offered X have subsequently disconnected, then X is no longer offered.

- A EbBody/EbClosure/transaction is _acquired/fetched/arrived_ if the node has already received, validated, and stored it.

- A request is _inflight_ if it has been issued AND its reply has not yet arrived.
  - Even if cancellation is sent, a degenerate reply is still expected.
    So sending a cancellation for some request does not directly affect whether it's inflight; it merely potentially causes its reply to arrive sooner.

- A EbBody/EbClosure/transaction is _inflight_ if a request for that datum is inflight UNLESS thatf datum has already arrived via the reply to some other request.

At the scale of the network:

- A EbBody/EbClosure/transaction is _diffusing_ as long as it's been offered to some honest nodes that are connected to the vast majority of honest stake AND there is still a non-trivial amount of honest stake that hasn't yet acquired it.

# High-Level Proposal

The following proposed LeiosFetch high-level behaviors are distill the components from the prior art that are applicable to LeiosFetch's challenges.

- Mitigate low quality connections and low-and-slow attacks via hedge requests and timeout-based disconnection (and maybe probation).
    - TODO choose the multiplicity and concrete rules for issuing hedge requests
    - TODO choose the concrete thresholds that incur disconnection/probation

- Request an EbClosure in several chunks spread across peers (say ~64 kB, like Solana's Turbine packets).
    - Unlike the abstract messages discussed in the Tail at Scale, EBs are not atomic ("Micro-partitions" is the corresponding nomenclature in that paper).
    - Chunking makes it possible to utilize multiple peers in parallel to fetch a single EB in a less wasteful way than merely sending completely redundant hedge requests to each peer.
    - Total redundancy among some chunk requests is still useful for reducing tail latency, but only once the still-missing portion of the EbClosure is small enough.
    - TODO actual rules for choosing chunk boundaries
    - TODO actual rules for issuing hedge requests as more peers offer the EB/peers disconnect/some replies arrive/etc

- Issue requests for EBs independently, regardless of any overlap between them.
    - This concern is separate from Mempool/TxCache; the Mempool/TxCache prevents requests for transactions that have already arrived rather than merely already being inflight.
    - In other words, the contents of the Mempool/TxCache suppress some LeiosFetch requests, but that's only their _current_ contents rather than their supposedly imminent contents.
    - Reason 1: the already-inflight request could be withheld/low-and-slowed, which would in turn delay the arrival of that transaction for the victim EB even if its actually being served.
    - Reason 2: Reason 1 does not apply among requests inflight with the same peer, but that case seems minor enough to not necessarily optimize.
      (TODO maybe intercontinental connections would see significant benefit?)

- If there are multiple EBs from which the node is missing transactions, prioritize sending the corresponding requests according to FreshestFirst.
  If some peers have not already offered the freshest of those EBs, allocate (TODO some but not all of?) their capacity to the already offered EBs.
    - A low-and-slow attack on the freshest EB must not stall all other EB diffusion (TODO at least not indefinitely).
    - TODO actual rules for rate-limiting each peer's requests (e.g. don't allocate more than its fair share of the local network stack to any single peer)
    - TODO actual rules for rate-limiting the cumulative requests across all peers (e.g. avoiding overloading the local network stack)

TODO Additional thoughts.

- TODO perhaps servers should tolerate some degree of optimism from client's, so that MsgLeiosBlockTxs might be allowed to arrive before the MsgLeiosBlockOffer is sent?
  That would hide the round-trip time between sending an offer and receiving the corresponding request.

- Possible optimization: notice when an already-sent chunk request becomes redundant due to _subsequent_ TxCache insertions, since doing so reduces the EB's latency.
    - Sending the cancellation as well in that case might avoid wasted upstream load.
      That's also good, but secondary.

- In practice, however, an EB will always be offered by one peer (likely/intended to be an intercontinental peer for intercontinental EBs) before any other peer offers it.
    - It'd be wasteful to not saturate that peer as soon as possible, so all chunks are instantly requested from that first peer.
      (Which its BDP might accommodate all at once.)
    - As offers arrive from other peers, hedge requests can be sent to them.
    - If those other peers outpace the first peer, then redundant requests can be sent to the fastest peers and cancellation requests sent to the first peer.
    - If a particular reply is taking longer than expected, additional hedge requests for the corresponding chunk will also be sent (TODO up to what limit?).
    - Send cancellations whenever a valid reply arrives.
      Thus, the first peer is likely to receive a request for all chunks but it will only actually serve whichever chunks it can manage to serve before other peers do.
