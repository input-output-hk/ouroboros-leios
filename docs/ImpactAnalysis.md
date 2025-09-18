# Introduction

This document is the first iteration of a high-level design for Linear Leios.
It is one of the next steps towards deriving an implementable design from [CIP-0164](https://github.com/cardano-foundation/CIPs/pull/1078).

(TODO This content is only for [the Consensus and Storage Layer](https://github.com/IntersectMBO/ouroboros-consensus) of [`cardano-node`](https://github.com/IntersectMBO/cardano-node) for now.)

# Vocabulary/Jargon

- Recall from CIP-0164 that an _endorser block_ (EB) is a list of cryptographic hashes that uniquely identify (serialized) transactions (including their signatures).
- Let an _EB's closure_ be the sequence of transactions referenced by an EB.
  Note that reconstructing an EB from its closure is merely a matter of calculating hashes.
- Recall from CIP-0164 that a _ranking block_ (RB) is merely a Praos block with a couple extra header fields and possibly containing a Leios certificate instead of Cardano transactions.
- The new RB header fields in particular include the hash of the EB issued alongside the RB, which _announces_ that EB.
- Let a _TxRB_ be an RB containing transactions and no certificate.
- Let a _CertRB_ be an RB containing a certificate and no transactions.
- Let a _CertRB's closure_ be the closure of the EB that it certifies.
- A vote _supports_ an RB header directly and its announced EB indirectly: if enough votes support the same RB header, then its announced EB can be included on chain.

# Requirements

This high-level design incorporates the following requirements from CIP-0164 into the existing code's architecture.
Subsequent sections will specify changes that satisfy these new requirements without introducing Denial of Service attack vectors, etc.

CIP-0164 implies the following functional requirements for the node.

- *REQ-IssueLeiosBlocks*.
  The node must issue an EB alongside each RB it issues, unless that EB would be empty.
- *REQ-IssueLeiosVotes*.
  The node must vote for EBs exactly according to the handful of rules from the CIP.
- *REQ-IncludeLeiosCertificates*.
  The node must include a certificate in each RB it issues if it has seen a quorum of votes for the EB issued alongside the preceding RB.
  (TODO excluding empty or very nearly empty EBs?)
- *REQ-DiffuseLeiosBlocks*.
  The node must run the new Leios mini-protocols alongside Praos to acquire and diffuse EBs and their closures.
- *REQ-DiffuseLeiosVotes*.
  The node must diffuse votes at least until they're old enough that there remains only a negligible probability they could still enable an RB that was issued on-time to include a certificate for the EB they support.
- *REQ-ArchiveLeiosBlocks*.
  The node must retain each EB's closure indefinitely when the settled Praos chain certifies it.

CIP-0164 also implies the following resource-management requirements for the node.

- *REQ-PrioritizePraosOverLeios*.
  The node must prioritize Praos traffic and computation over all Leios traffic and computation so that the diffusion and adoption of any RB is only negligibly slower.
- *REQ-PrioritizeFreshOverStaleLeios* (aka _freshest first delivery_).
  The node must prioritize Leios traffic and computation for younger EBs over Leios traffic and computation for older EBs so that a _protocol burst attack_ (see below) cannot significantly degrade Leios throughput.

These two rules can be summarized as Praos &gt; fresh Leios &gt; stale Leios.

Looking forward, Peras should also be prioritized over Leios, since a single Peras failure is more disruptive (to Praos, even!) than a single Leios failure.
It's not yet clear how priority relates Peras and Praos, but that's beyond the scope this document.

# Consensus Changes for Functional Requirements

- *UPD-LeiosAwareBlockProductionThread*, for REQ-IssueLeiosBlocks and REQ-IncludeLeiosCertificates.
  The existing block production thread must generate an EB at the same time it generates an RB.
  In particular, the hash of the EB is a field in the RB header, and so the RB header can only be decided after the EB is decided, and that can only be after the RB payload is decided; it's intertwined enough to justify doing it in a single thread.
  Moreover, the RB payload is either a certificate or transactions, and that must also be decided by this thread.
- *UPD-LeiosBiggerMempool*, for REQ-IssueLeiosBlocks, actually utilizing the Leios capacity, and incentives.
  The Mempool capacity should at least be twice the capacity of an EB, so that the stake pool issuing a CertRB for a full EB would still be able to issue a full EB alongside that CertRB (TxRB's have less transaction capacity than the EB certified by a CertRB).
  In general, SPOs are indirectly incentivized to maximize the size of the EB, just like TxRBs---so that more fees are included in the epoch's reward calculation.
  Thus the Mempool's capacity should be increased so that it can hold enough valid transactions for the block producer to issue a full EB alongside a full RB.
- *NEW-LeiosVoteProductionThread*, for REQ-IssueLeiosVotes.
  A thread dedicated to Leios vote production will wake up when the closure of a EB is newly available.
  If the voting rules would require the stake pool to vote (now or soon) for this EB if it's valid, then this thread will begin validating it.
  Note if multiple closures arrive simultaneously, at most one of them could be eligible for a vote, since the voting rules require the EB to be announced by the tip of the node's current selection.
  If the validation succeeds while the voting rules still require the stake pool to vote for this EB (TODO even if it has since switched its selection?), the thread will issue that vote.
- *NEW-LeiosVoteStorage*, for REQ-DiffuseLeiosVotes and REQ-IncludeLeiosCertificates.
  A new storage component will store all votes received by a node, up to some conservative age (eg ten minutes).
  As votes arrive, they will be grouped according to the RB they support.
  When enough votes have arrived for some RB, the certificate can be generated immediately, which can avoid delaying the potential subsequent issuance of a CertRB by this node.
  A vote for the EB announced by an RB is irrelevant once all nodes will never switch their selection away from some block that is not older than that RB.
  This condition is very likely to be satisifed relatively soon on Cardano mainnet, unless its Praos growth is being disrupted, in which case reduced Leios throughput would be a less important problem.
  Therefore, the vote storage component can simply discard votes above some conservative age, which determines a stochastic upper bound the heap size of all sufficiently-young votes.
- *NEW-LeiosEbStore*, for REQ-DiffuseLeiosBlocks and REQ-ArchiveLeiosBlocks.
  Unlike votes, a node should retain the closures of older EB, because Praos allows for occasional deep forks, the most extreme of which could require the closure of an EB that was announced by the youngest block in the Praos Common Prefix.
  On Cardano mainnet, that RB is usually 12 hours old, but could be up to 36 hours old before [CIP-0135 Disaster Recovery Plan](https://cips.cardano.org/cip/CIP-0135) is triggered.
  Thus, EB closures are not only large but also have a prohibitively long lifetime even when they're ultimately not immortalized by the historical chain.
  This component therefore stores EBs on disk just as the ChainDB already does for RBs.
  The volatile and immutable dichotomy can even be managed the same way it is for RBs.
- *NEW-LeiosCertRbStagingArea*, for REQ-DiffuseLeiosBlocks.
  Each CertRB must be buffered in a staging area until its closure arrives, since the VolDB only contains RBs that are ready for ChainSel.
  (Note that a CertRB's closure will usually have arrived before it did.)
  (TODO Any disadvantages? For example, would it be beneficial to detect an invalid certificate before the closure arrives?)
  (TODO a more surgical alternative: the VolDB index could be aware of which EB closures have arrived, and the path-finding algorithm could incorporate that information.
   However, this means each EB arrival may need to re-trigger ChainSel.)
- *UPD-LeiosRbBlockFetchClient*, for REQ-DiffuseLeiosBlocks.
  Therefore, the BlockFetch client must only directly insert a CertRB into the VolDB if its closure has already arrived (which should be common due to L_diff).
  Otherwise, the CertRB must be deposited in the CertRB staging area instead.
- *UPD-LeiosLedgerDb*, for REQ-DiffuseLeiosBlocks.
  The LedgerDB will need to retrieve the certified EB's closure from the LeiosEbStore when applying a CertRB.
  Due to NEW-LeiosCertRbStagingArea, it should be impossible for that retrieval to fail.
- *NEW-LeiosTxCache*, for REQ-DiffuseLeiosBlocks and (via NEW-LeiosVoteProductionThread) REQ-IssueLeiosVotes.
  A new storage component will store all transactions received when diffusing EBs as well as all transactions that successfully enter the Mempool, up to some conservative age (eg one hour).
  The fundamental reason that EBs refer to transactions by hash instead of including them directly is that, for honest EBs, the node will likely have already received most of the referenced transactions when they recently diffused amongst the Mempools.
  That's not guaranteed, though, so the node must be able to fetch whichever transactions are missing, but in the absence of an attack that ought to be minimal.
  The Mempool is the natural inspiration for this optimization, but it's inappropriate as the actual cache for two reasons: it has a relatively small, multidimensional capacity and its eviction policy is determined by the distinct needs of block production.
  This new component instead has a greater, unidimensional capacity and a simple Least Recently Used eviction policy.
- *NEW-LeiosMiniProtocols*, for REQ-DiffuseLeiosBlocks, REQ-DiffuseLeiosVotes, and REQ-ArchiveLeiosBlocks.
  The node must include new mini-protocols to diffuse EB announcements, EBs themselves, EBs' transactions, and votes for EBs.
- *NEW-LeiosFetchDecisionLogic*, for REQ-DiffuseLeiosBlocks, REQ-DiffuseLeiosVotes, and REQ-ArchiveLeiosBlocks.
  The Leios mini-protocols will require new fetch decision logic, since the node should not necessarily simply download every such object from every peer that offers it.
  Such fetch decision logic is also required for TxSubmission and for Peras votes; the Leios logic will likely be similar but not equivalent.

# Protocol Burst Attack

There are multiple attack vectors against Leios, but one is particularly relevant to resource-management.

- *ATK-LeiosProtocolBurst*.
  In a protocol burst attack the adversary withholds a large number of EBs and/or their closures over a significant duration and then releases them all at once.
  This will lead to a sustained maximal load on the honest network for a smaller but still significant duration, a.k.a. a burst.

The potential magnitude of that burst will depend on various factors, including at least the adversary's portion of stake, but the worst-case is more than a gigabyte of download.
The cost to the victim is merely the work to acquire the closures and to check the hashes of the received EB bodies and transaction bodies.
In particular, at most one of the EBs in the burst could extend the tip of a victim node's current selection, and so that's the only EB the victim would attempt to fully parse and validate.

# Risks Threatening the Resource-Management Requirements

The fundamental idea behind Leios has always been that the Praos protocol is inherently and necessarily bursty.
Leios should be able to freely utilize the nodes' resources whenever Praos is not utilizing them, which directly motivates REQ-PrioritizePraosOverLeios.
It is ultimately impossible to achieve such time-multiplexing perfectly, due to the various latencies and hystereses inherent to the commodity infrastructure (non real-time operating systems, public Internet, etc).
On the other hand, it is also ultimately unnecessary to time-multiplex Praos and Leios perfectly, but which degree of imperfection is tolerable?

Contention for the following primary node resources might unacceptably degrade the time-multiplexing via contention between Praos and Leios.

- *RSK-LeiosPraosContentionNetworkBandwidth*.
  This is not anticipated to be a challenge, because time-multiplexing the bandwidth is relatively easy.
  In factor, Leios traffic while Praos is idle could potentially even prevent the TCP Receive Window from contracting, thus avoiding a slow start when Praos traffic resumes.
- *RSK-LeiosPraosContentionCPU*.
  This is not anticipated to be a challenge, because today's Praos node does not exhibit major CPU load on multi-core machines.
  Leios might have more power-to-weight ratio for parallelizing its most expensive task (EB validation), but that parallelization isn't yet obviously necessary.
  Thus, even Praos and Leios together do not obviously require careful orchestration on a machine with several cores.
- *RSK-LeiosPraosContentionGC*.
  It is not obvious how to separate Peras and Leios into separate OS processes, since the ledger state is expensive to maintain and both protocols frequently read and update it.
  When the Praos and Leios components both run within the same operating system process, they share a single instance of the GHC Runtime System (RTS), including eg thread scheduling and heap allocation.
  The sharing of the heap in particular could result in contention, especially during an ATK-LeiosProtocolBurst (at least the transaction cache will be doing tens of thousands of allocations, in the worst-case).
  Even if the thread scheduler could perfectly avoid delaying Praos threads, Leios work could still disrupt Praos work, because some RTS components exhibit hysteresis, including the heap.
- *RSK-LeiosPraosContentionDiskBandwidth*.
  Praos and Leios components might contend for disk bandwidth.
  In particular, during a worst-case ATK-LeiosProtocolBurst, the Leios components would be writing more than a gigabyte to disk as quickly as the network is able to acquire the bytes (from multiple peers in parallel).
  Praos's disk bandwidth utilization depends on the leader schedule, fork depth, etc, as well as whether the node is using a non-memory backend for ledger storage (aka UTxO HD or Ledger HD).
  For non-memory backends, the ledger's disk bandwidth varies drastically depending on the details of the transactions being validated and/or applied: a few bytes of transaction could require thousands of bytes of disk reads/writes.
    - Note that the fundamental goals of Leios will imply a significant increase in the size of the UTxO.
      In response, SPOs might prefer enabling UTxO HD/Ledger HD over buying more RAM.

Both GC pressure and disk bandwidth are notoriously difficult to model and so were not amenable to the simulations that drove the first version of the CIP.
Prototypes rather than simulations will be necessary to assess these risks with high confidence.

The same risks can also be viewed from a different perspective, which is more actionable in terms of planning prototypes/experiements/etc: per major component of the node.

- *RSK-LeiosLedgerOverheadLatency*.
  Parsing a transaction, checking it for validity, and updating the ledger state accordingly all utilize CPU and heap (and also disk bandwidth with UTxO/Ledger HD).
  Frequent bursts of that resource consumption proportional to 15000% of a full Praos block might disrupt the caught-up node in heretofore unnoticed ways.
  Only syncing nodes have processed so many/much transactions in a short duration, and latency has never been a fundamental priority for a syncing node.
  Disruption of the RTS is the main concern here, since there is plenty of CPU available—the ledger is not internally parallelized, and only ChainSel and the Mempool could invoke it simultaneously.
- *RSK-LeiosNetworkingOverheadLatency*.
  Same as RSK-LeiosLedgerOverheadLatency, but for the Diffusion Layer components handling frequent 15000% bursts in a caught-up node.
- *RSK-LeiosMempoolOverheadLatency*.
  Same as RSK-LeiosLedgerOverheadLatency, but for the Mempool frequently revalidating 15000% load in a caught-up node during congestion (ie 30000% the capacity of a Praos block, since the Leios Mempool capacity is now two EBs instead of two Praos blocks).
- _Etc_

# Prototypes and Experiments for Derisking Resource-Management

The first new code will be used to demonstrate and measure the contention underlying the above risks.
The following experiments each pertain to several of the risks above.

- *EXP-LeiosLedgerDbAnalyser*.
  A new pass in [`db-analyser`](https://github.com/IntersectMBO/ouroboros-consensus/blob/main/ouroboros-consensus-cardano/README.md#db-analyser) will enable an experiment to analyse the CPU and GC costs of processing a sequence of realistic transactions that corresponds to the full capacity of an EB.
  Ledger state snapshot files and contiguous blocks can be sliced from `mainnet`, P&T clusters, etc to assemble a sequence of transactions that could be collated by an EB.
  Both full validation (eg Leios voting) as well as mere reapplication (eg Mempool) should be separately analyzed.
  This experiment will record and summarize the observed behavior of the mutator time and various GC statistics, so as to inform futher consideration of risks as well as the design of other experiments (eg traffic shaping).
- *EXP-LeiosDiffusionOnly*.
  A minimally-patched Praos node can include only the Leios changes necessary to actually diffuse EBs and their closures.
  Notably, even the content of the transactions in the EBs need not be well-formed.
    - This patched node will assume every EB is worthy of certification but somehow never influences the ledger state.
    - In order for Praos headers to suffice, EBs in this patched system will list the "announcing" header's hash, which is fine since EBs are trustworthy in this experiment.
    - In this experiment, EBs' transactions merely need to be diffused, hash checked, and stored---not even parsed.
      Every transaction within an EB will be an opaque bytestring (with random contents to avoid accidental trivialities).
      The complementary EXP-LeiosLedgerDbAnalyser experiment will characterize which resource consumption this choice avoids, which is useful for avoiding conflation.
    - Each RB permitted to contain a certificate is blocked (in the NEW-LeiosCertRbStagingArea) by the arrival of its predecessor's announced EB, but Praos is otherwise unaffected.
    - Mocked upstream peers will originate all blocks, and the node(s) under test will merely relay everything.
      The incoming RBs could simply be copied from `mainnet`, a P&T cluster run, etc, with the EBs' fully mocked arrival times derived in some way from the original RBs' slot onsets.
    - This experiment will analyze the GC stats and other event logs of the node(s) under test.
    - TODO what about TxSubmission traffic?

# Consensus Changes for Resource-Management Requirements

It is not already clear which new or updated mechanisms/components would mitigate the resource-management risks, if the prototypes and experiment indicate mitigations are necessary.

- For REQ-PrioritizePraosOverLeios, RSK-LeiosPraosContentionGC could possibly be mitigated via an adaptation of UTxO HD.
  Leios transaction parsing and processing could be isolated in a separate process which uses a UTxO HD-like interface in order to access the necessary UTxO from the Praos process.
  The additional overhead of transferring the relevant UTxO along IPC channels might be an acceptable cost for isolating the Leios GC pressure.
    - The developers of GHC Haskell have considered a separation mechanism called GHC Execution Domains intended to significantly mitigate this class of risk, but it has not yet matured past ideation.
      See ["Erlang-style processes in the RTS"](https://gitlab.haskell.org/ghc/ghc/-/issues/21578) and ["Execution domains in GHC/Haskell" (HIW23 Lightning Talk)](https://www.youtube.com/watch?v=Ha7oIVrLwSI).
- RSK-LeiosPraosContentionDiskBandwidth could be mitigated by rate-limiting the Leios disk traffic, with back pressure to accordingly rate-limit the Leios network traffic.

# TODO some concrete Consensus details

- First version of LedgerDB need not explicitly store EB's ledger state; the CertRB's result ledger state will reflect the EB's contents.
  Second version could thunk the EB's reapplication alongside the announcing RB?
  That would only avoid reapplication of one EB on a chain switch (might be worth it for supporting tiebreakers?).
- First version of LedgerDB can simply reapply the EB's transactions before tick-then-applying a CertRB.
  Second version should pass the EB's transactions to the ledger function (or instead the thunk of reapplying the EB)?
- First version of the Mempool can be naive, the block production thread will handle everything.
  Second version can try to pre-compute in order to avoid delays (ie discarding the certified EB's chunk of transactions) when issuing a CertRB and its announced EB.
- First version of LeiosTxCache should reliably cache all relevant transactions that are less than an hour or so old---that age spans 180 active slots on average.
  A transaction is born when its oldest containing EB was announced or when it _entered_ the Mempool (if it hasn't yet been observed in an EB).
  (Note that that means some tx's age in the LeiosTxCache can increase when an older EB that contains it arrives.)
  Simple index maintained as a pair of a priority queues (index and age) in manually managed fixed size bytearrays, backed by a double-buffered mmapped file for the transactions' serializations.
  Those implementation choices prevent the sheer number of transactions from increasing GC pressure (adversarial load might lead to a ballpark number of 131000 transactions per hour), and persistence's only benefit here would be to slightly increase parallelism/simplify synchronization, since persistence would let readers release the lock before finishing their search.
- Note: if all possibly-relevant EBs needed to fit in the LeiosTxCache, its worst case size would approach 500 million transactions.
  Even the index would be tens of gigabytes.
  This is excessive, since almost all honest traffic will be younger than an hour---assuming FFD is actually enforced.
- First version of LeiosFetch client can assemble the EB closure entirely on disk, one transaction at a time.
  Second version might want to batch the writes in a pinned mutable `ByteArray` and use `withMutableByteArrayContents` and `hPutBuf` to flush each batch.
  Again, the possible benefit of this low-level shape would be to avoid useless GC pressure.
- First version of LeiosFetch client can wait for all transactions before starting to validate any.
  Later version could eagerly validate as the prefix arrives---comparable to eliminating one hop in the topology, in the worst-case scenario.
- First version of LeiosFetch server simply pulls serialized transactions from the LeiosEbStore, and only sends notifications to peers that are already expecting them when the noteworthy event happens.
  If notification requests and responses are decoupled in a separate mini protocol _or else_ requests can be reordered (TODO or every other request supports a "MsgOutOfOrderNotificationX" loopback alternative?), then it'll be trivial for the client to always maintain a significant buffer of outstanding notification requests.
- Even the first version of LeiosFetch decision logic should consider EBs that are certified on peers' ChainSync candidates as available for request, as if that peer had sent both MsgLeiosBlockOffer and MsgLeiosBlockTxsOffer.
  A MsgRollForward implies the peer has selected the block, and the peer couldn't do that for a CertRB if it didn't already have its closure.
- First version of LeiosEbStore can just be two bog standard key-value stores, one for immutable and one for volatile.
  Second version maybe instead integrates certified EBs into the existing ImmDB?
  That integration seems like a good fit.
  It has other benefits (eg saves a disk roundtrip and exhibits linear disk reads for driver prefetching/etc), but those seem unimportant so far.
