---
sidebar_position: 6
---

# FAQs

## What is Ouroboros Leios?

Ouroboros Leios is a next-generation blockchain consensus protocol designed to
make Cardano faster and more scalable. It improves transaction throughput and
reduces latency by splitting the work of processing transactions into a
streamlined, parallel process. Building on the core Ouroboros principles (as
used by Cardano), Leios introduces separate input blocks (IBs) for transactions
and endorser blocks (EBs) that validate them, enhancing the network’s capacity.

## What are the key benefits of Leios over other Ouroboros protocols?

Leios offers several significant advantages:

- **Higher throughput and lower latency:** by splitting transaction processing
  into IB and EB stages, Leios handles more transactions in parallel, enabling
  faster and more responsive applications
- **Better user experience:** faster transaction processing means quicker
  confirmations for wallet users and DApp interactions
- **Flexible diffusion strategies:** nodes can choose how to share blocks (eg,
  prioritizing the newest or the oldest data), optimizing network performance based on
  conditions
- **Enhanced cryptography:** Leios uses Boneh–Lynn–Shacham (BLS) signatures for
  aggregated verification and verifiable random functions (VRFs) for fair leader
  selection
- **Robust simulations and formal methods:** Rust and Haskell simulations
  measure real-world performance, and executable specifications ensure
  correctness
- **Scalable cost model:** a cost calculator helps node operators estimate
  expenses (for example, storage and CPU usage).

## What does Leios mean for Cardano users (eg, wallet users, DApp developers)?

For everyday users, Leios means faster transaction confirmations and a smoother
experience in wallets and DApps—think near-instant payments or interactions
instead of waiting 20 seconds or more. For developers, it offers higher
throughput (more transactions per second), enabling complex, high-volume
applications like decentralized exchanges or gaming platforms. However, wallets,
explorers, and APIs will need updates to handle Leios’ new block types (IBs,
EBs, RBs), so expect some transition as it rolls out.

## What are the risks or trade-offs of Leios?

Leios prioritizes scalability, but it’s not without trade-offs. Parallel
processing increases demands on node operators (eg, more CPU, bandwidth,
storage), potentially raising costs or requiring better hardware. The complexity
of the three block types (IBs, EBs, RBs) could also introduce new bugs or delays
during implementation. However, extensive simulations and formal methods aim to
minimize these risks, ensuring Leios remains secure and reliable as it matures.

## What are IBs, EBs, and RBs in Leios?

Leios uses three distinct block types:

- **IB (input block)**. A block that contains transactions. Produced by nodes
  that win the IB sortition lottery.
- **EB (endorser block)**. A block that references one or more IBs, providing
  endorsements. Produced by nodes that win the EB sortition lottery.
- **RB (ranking block)**. A block that ranks or orders other blocks as part of
  the consensus mechanism.

Each block type plays a distinct role in moving transactions from submission to
final confirmation. IBs are minted frequently, EBs validate in parallel, RBs
occur every ~20 seconds.

## What is the relationship between Ouroboros, Peras, and Leios?

### Ouroboros: the foundation

- What it is: Ouroboros is the overarching family of proof-of-stake (PoS)
  consensus protocols that powers Cardano. It’s designed to be secure,
  energy-efficient, and provably fair, replacing proof-of-work (PoW) systems
  like Bitcoin’s.
- Key features:
  - Slot-based time division (epochs and slots, with slots typically 1 second
    long in earlier versions, now 20 seconds in Praos for block production)
  - Stake pool leaders elected based on stake to mint blocks
  - Formal mathematical proofs of security (for example, resistance to attacks like
    double-spending or chain forks)
- Role: Ouroboros is the bedrock consensus mechanism that Peras and Leios build
  upon or refine.

### Peras: a modular upgrade

- What it is: Peras is a proposed evolution of Ouroboros aimed at improving
  efficiency and modularity.
- Key features:
  - Separation of concerns. Peras splits consensus into modular components, such
    as transaction ordering, validation, and ledger state updates, to allow
    parallel processing and flexibility.
  - Improved finality. It introduces mechanisms for faster confirmation times.
  - Separation of concerns. Peras splits consensus into modular components, such
    as transaction ordering, validation, and ledger state updates to allow
    parallel processing and flexibility.
  - Improved finality. It introduces mechanisms for faster confirmation times,
    potentially reducing the time to finality compared to Praos’ 20-second block
    intervals.
  - Adaptability. Designed to integrate with future scaling solutions (like
    Leios) and sidechains or layer-2 systems.
- Relationship to Ouroboros:
  - Peras is a direct descendant of Ouroboros Praos, refining its mechanics
    while staying within the PoS framework. It’s like an 'Ouroboros 2.0,'
    optimizing the core protocol without fundamentally changing its PoS nature.
  - It serves as a bridge between the foundational Ouroboros Praos and more
    radical scalability-focused variants like Leios.

### Leios: a scalability leap

- What it is: Ouroboros Leios is a specific variant of the Ouroboros family,
  designed to dramatically increase Cardano’s throughput (transactions per
  second, TPS) while maintaining security. It’s an experimental or future-state
  protocol, not yet live as of March 2025, but actively discussed in Cardano’s
  research community.
- Relationship to Ouroboros:
  - Leios is a specialized extension of Ouroboros, taking the core PoS mechanics
    and re-architecting block production for scalability.
  - It retains Ouroboros’ security model but reimagines how transactions are
    ingested and validated, making it a next-generation Ouroboros variant.

### The relationship

- Ouroboros as the core:
  - Ouroboros (especially Praos) is the foundational consensus protocol that
    defines Cardano’s PoS system. Both Peras and Leios are built on this
    foundation, inheriting its security properties and stake-based governance.
- Peras as an intermediate step:
  - Peras enhances Ouroboros by introducing modularity and efficiency
    improvements, potentially laying the groundwork for integrating advanced
    features like those in Leios. It’s a stepping stone that refines Praos’
    mechanics, making it more adaptable to future needs.
- Leios as a scalability solution:
  - Leios takes Ouroboros further by addressing throughput limitations head-on.
    It uses the same PoS principles but introduces a parallel processing model
    that Peras’ modularity could theoretically support or complement.
  - Leios can be seen as a 'plugin' or evolution that fits into the Ouroboros
    ecosystem, possibly relying on Peras’ groundwork for smoother integration.
- Timeline and evolution:
  - Ouroboros Praos → current live protocol.
  - Peras → a near-future refinement for flexibility and efficiency.
  - Leios → a long-term scalability solution, still in research/development,
    aimed at making Cardano competitive with high-TPS blockchains like Solana or
    Ethereum layer-2s.

## What's the state of an IB before an EB or RB gets created for it? Is it visible, is it usable?

Before an endorsement block (EB) or ranking block (RB) is created, an input
block (IB) is a proposed set of transactions in a preliminary state. Here’s what
that means:

### State of an IB

An IB is minted by a node (eg, a stake pool operator) and contains unconfirmed
transactions from the mempool. It’s cryptographically signed for authenticity
but hasn’t been validated or finalized by the network, leaving it in a pending
state.

### Visibility

Once minted, the IB is broadcast and visible to all nodes. This allows them to
inspect its transactions and start validation, a key part of Leios’ parallel
processing design. However, visibility doesn’t mean it’s accepted — it’s just a
proposal.

### Usability

The IB isn’t usable yet — its transactions can’t be spent or relied upon because
they lack consensus and finality. Only after EBs endorse it and an RB finalizes
it does it become part of the blockchain’s official state. Until then, it could
still be discarded if it fails validation.

## If an IB isn't really usable until it's got an EB and RB, and RB's still take 20 seconds, how does this improve performance?

Leios boosts performance by processing transactions in parallel, even though
final confirmation still takes 20 seconds. Here’s how:

### Parallel processing boost

Think of Leios like a factory: in Ouroboros Praos, one worker (a slot leader)
builds a block every 20 seconds. In Leios, dozens of workers (nodes) create
IBs continuously, others check them with EBs, and a supervisor (RB) approves the batch every 20 seconds.
This parallelism lets the network handle far more transactions in that
time — potentially 10x to 100x more than Praos.

### Splitting the work

- **IBs**. Propose transactions frequently and in parallel.
- **EBs**. Validate IBs concurrently across nodes.
- **RBs**. Finalize everything every 20 seconds, ensuring security. Unlike
  Praos, where one block does it all, Leios splits these roles so transaction
  processing isn’t bottlenecked by the 20-second RB interval.

### Practical gains

While IBs aren’t spendable until an RB confirms them, EBs provide early
confidence, letting apps (like wallets) act on them sooner for low-risk tasks
(for example, showing balances). The 20-second RB is a security anchor, not a
limit—hundreds of IBs can queue up in that window, massively increasing
throughput.

## How does Leios maintain security with parallel processing?

Leios preserves Cardano’s strong security by combining parallel transaction
processing with a sequential finality layer. IBs and EBs are produced in parallel, but RBs finalize the
ledger every 20 seconds, ensuring a single, consistent chain. This prevents
double-spending or forks by resolving conflicts at the RB stage. Additionally,
cryptographic tools like BLS signatures and VRFs ensure that only valid blocks
from authorized nodes are accepted, maintaining Ouroboros’ provable security
guarantees.

## How does Leios handle voting stages, and what is 'send-recv' voting?

Leios finalizes blocks through a structured voting mechanism. Nodes may adopt:

- **Single-stage voting**: all votes are broadcast in one phase, possibly
  resulting in a longer CPU usage 'tail' during high throughput
- **Send-recv (two-stage) voting**: votes are first sent, then a follow-up
  receive phase ensures broader propagation before final tallies.

You can configure voting through parameters such as leios-vote-send-recv-stages
in simulation environments.

## What is sortition in Leios, and how does 'Fait Accompli sortition' work?

Sortition is a probabilistic method for selecting nodes (based on stake) to
produce blocks or issue votes. In Leios, it is referred to as 'Fait Accompli
sortition' because once a node proves it was selected to produce a block or vote
(using a cryptographic proof), no conflicting claims can arise.

## What are the different block diffusion strategies, and why do they matter?

Leios supports multiple strategies for propagating blocks and votes:

- **Oldest-first**: prioritizes older blocks or transactions
- **Freshest-first**: focuses on the newest blocks or transactions first
- **Peer-order**: requests blocks in the order peers announce them.

Your choice of strategy can affect latency, network load, and overall
throughput.

## Can the system be sharded or self-regulated?

Not in its current design. Every node validates the entire chain. Thus, adding
more nodes does not inherently increase throughput in the same way sharded
protocols do. The community votes on protocol parameters (for example, block
size), and the system's load is the same for all. Future research may explore
sharding, but it is not yet part of Leios.

## What improvements in cryptography are used in Leios?

Leios incorporates multiple cryptographic techniques to ensure security and
efficiency:

- BLS signatures: allow efficient aggregation of many signatures into one,
  reducing verification overhead
- Mithril or Musen protocols: used for voting and proof aggregation, depending
  on the context
- VRFs: ensure fair selection of nodes for block production.

Recent benchmarking shows that aggregated BLS verification significantly speeds
up certificate validation.

## How do I estimate node operating costs for Leios?

Leios provides an online cost calculator that considers:

- **CPU usage and the number of cores**
- **Bandwidth consumption**
- **Storage** (including the default assumption of 50% disk compression)
- **Perpetual storage cost amortization**.

It also supports hyperscale and discount cloud providers. For example, you can
model single-relay or multi-relay deployments at variable bandwidths.

## What is the current status of Leios simulations?

Two primary simulation frameworks (Rust and Haskell) are maintained to:

- Test network topologies and measure real or simulated latencies (using the
  DeltaQ model)
- Evaluate CPU usage for blocks and transactions under varying loads
- Visualize block diffusion (IBs, EBs, and RBs) using different strategies
- Compare ideal conditions vs realistic mainnet-like topologies.

Developers continually refine these simulations based on real-world data.

## Are there recommended parameters for running Leios nodes?

Based on preliminary internal testing and simulations:

- **Block size**: commonly set to about one-third of the available link capacity
  for IBs
- **Voting stages**: choose single-stage or send-recv, depending on reliability
  and speed requirements
- **Diffusion strategy**: many operators use 'freshest-first,' though
  'peer-order' may help maintain compatibility with older setups.

Operators can adjust these parameters, which evolve through community votes.

## How do I keep track of Leios's progress and updates?

You can follow:

- Weekly updates on the Ouroboros Leios site
- Technical reports for deeper insights
- Leios glossary for definitions of commonly used terms
- Public GitHub repositories that host source code and simulations.

These resources provide transparency and regular updates on ongoing development.

## What are the downstream effects of deploying Leios?

Leios changes how transactions are validated and how blocks and memory pools
operate, potentially affecting:

- **Wallets and SDKs**, which need to accommodate new block types (IBs and EBs)
- **Explorers**, which must handle higher throughput and multi-block referencing
- **Indexers and APIs**, which will see more granular block and vote data.

Weekly updates provide a deeper analysis of these topics, including how advanced
indexing and potential sharding solutions might eventually mitigate challenges.

## Could the mempool be sized according to the system's throughput?

That's already the case. The default mempool size is a small multiple of the
current block size.

## Is Leios production-ready?

Leios remains an active research and development protocol. It is backed by a
robust formal methods framework and two major simulation environments. However,
it has not reached full production status. Watch the official updates and
technical reports for major release announcements.
