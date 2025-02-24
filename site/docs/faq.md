---
sidebar_position: 6
---

# FAQs

## What is Ouroboros Leios?

Ouroboros Leios is a next-generation blockchain consensus protocol designed to improve transaction throughput and reduce latency by using a pipelined endorsing process. It builds upon the core Ouroboros principles (as used by Cardano), introducing separate input blocks (IBs) for transactions and endorser blocks (EBs) that reference those transactions, thus enhancing scalability.

## What are the key benefits of Leios compared with traditional Ouroboros?

Leios offers several significant advantages:

- **Higher throughput and lower latency.** By splitting transaction processing into IB and EB stages, Leios handles more transactions in parallel.
- **Flexible diffusion strategies.** Nodes can choose different block-propagation methods, such as 'freshest-first' or 'oldest-first.'
- **Enhanced cryptography.** Leios uses BLS (Boneh–Lynn–Shacham) signatures for aggregated verification and verifiable random functions (VRFs) for leader selection.
- **Robust simulations and formal methods.** Rust and Haskell simulations measure real-world performance, and executable specifications help ensure correctness.
- **Scalable cost model.** A cost calculator enables node operators to estimate expenses (for example, storage amortization and CPU usage).

## What are IBs, EBs, and RBs in Leios?

Leios uses three distinct block types:

- IB (input block): a block that contains transactions. Produced by nodes that win the IB sortition lottery.
- EB (endorser block): a block that references one or more IBs, providing endorsements. Produced by nodes that win the EB sortition lottery.
- RB (ranking block): a block that ranks or orders other blocks as part of the consensus mechanism.

Each block type plays a distinct role in moving transactions from submission to final confirmation.

## How does Leios handle voting stages, and what is 'send-recv' voting?

Leios finalizes blocks through a structured voting mechanism. Nodes may adopt:

- Single-stage voting: all votes are broadcast in one phase, possibly resulting in a longer CPU usage 'tail' during high throughput.
- Send-recv (two-stage) voting: votes are first sent, then a follow-up receive phase ensures broader propagation before final tallies.

You can configure voting through parameters such as leios-vote-send-recv-stages in simulation environments.

## What is sortition in Leios, and how does 'Fait Accompli sortition' work?

Sortition is a probabilistic method for selecting nodes (based on stake) to produce blocks or issue votes. In Leios, it is referred to as 'Fait Accompli sortition' because once a node proves it was selected to produce a block or vote (using a cryptographic proof), no conflicting claims can arise.

## What are the different block diffusion strategies, and why do they matter?

Leios supports multiple strategies for propagating blocks and votes:

- Oldest-first: prioritizes older blocks or transactions
- Freshest-first: focuses on the newest blocks or transactions first
- Peer-order: requests blocks in the order peers announce them

Your choice of strategy can affect latency, network load, and overall throughput.

## Can the system be sharded or self-regulate?

Not in its current design. Every node validates the entire chain. Thus, adding more nodes does not inherently increase throughput in the same way sharded protocols do. The community votes on protocol parameters (for example, block size), and the system's load is the same for all. Future research may explore sharding, but it is not yet part of Leios.

## What improvements in cryptography are used in Leios?

Leios incorporates multiple cryptographic techniques to ensure security and efficiency:

- BLS signatures: allows efficient aggregation of many signatures into one, reducing verification overhead
- Mithril or Musen protocols: used for voting and proof aggregation, depending on the context
- VRFs: ensures fair selection of nodes for block production

Recent benchmarking shows that aggregated BLS verification significantly speeds up certificate validation.

## How do I estimate node operating costs for Leios?

Leios provides an online cost calculator that considers:

- CPU usage and the number of cores
- Bandwidth consumption
- Storage (including the default assumption of 50% disk compression)
- Perpetual storage cost amortization

It also supports hyperscale and discount cloud providers. For example, you can model single-relay or multi-relay deployments at variable bandwidths.

## What is the current status of Leios simulations?

Two primary simulation frameworks (Rust and Haskell) are maintained to:

- Test network topologies and measure real or simulated latencies (using the DeltaQ model)
- Evaluate CPU usage for blocks and transactions under varying loads
- Visualize block diffusion (IBs, EBs, and RBs) using different strategies
- Compare ideal conditions vs realistic mainnet-like topologies

Developers continually refine these simulations based on real-world data.

## Are there recommended parameters for running Leios nodes?

Based on preliminary internal testing and simulations:

- Block size: commonly set to about one-third of the available link capacity for IBs
- Voting stages: choose single-stage or send-recv, depending on reliability and speed requirements
- Diffusion strategy: many operators use 'freshest-first,' though 'peer-order' may help maintain compatibility with older setups

Operators can adjust these parameters, which evolve through community votes.

## How do I keep track of Leios's progress and updates?

You can follow:

- Weekly progress updates on the Ouroboros Leios site
- Technical reports for deeper insights
- Leios glossary for definitions of commonly used terms
- Public GitHub repositories that host source code and simulations

These resources provide transparency and regular updates on ongoing development.

## What are downstream effects of deploying Leios?

Leios changes how transactions are validated and how blocks and memory pools operate, potentially affecting:

- Wallets and SDKs, which need to accommodate new block types (IBs and EBs)
- Explorers, which must handle higher throughput and multi-block referencing
- Indexers and APIs, which will see more granular block and vote data

Weekly progress updates provide deeper analysis of these topics, including how advanced indexing and potential sharding solutions might eventually mitigate challenges.

## Could the mempool be sized to the throughput of the system?

That's already the case. Default mempool size is a small multiple of current block size.

## Is Leios production-ready?

Leios remains an active research and development protocol. It is backed by a robust formal methods framework and two major simulation environments. However, it has not reached full production status. Watch the official progress updates and technical reports for major release announcements.
