---
sidebar_position: 6
---

# FAQs

## What is Ouroboros Leios?

Ouroboros Leios is a next-generation consensus protocol designed to significantly accelerate and scale Cardano. It improves transaction throughput and reduces latency by splitting transaction processing into parallel stages while preserving Cardano’s core security and decentralization. To learn more, visit the [Leios development tracker](https://engineering.iog.io/leios).

## What are the key benefits of Leios over other Ouroboros protocols?

Leios delivers several major improvements:

-   **Much higher throughput**: up to 1,500+ transactions per second (30–65× current Praos levels)
-   **Faster transaction inclusion**: parallel processing allows many more transactions to be handled quickly
-   **Better user experience**: smoother wallets, decentralized finance (DeFi), non-fungible tokens (NFTs), gaming, and high-volume applications
-   **Flexible diffusion and voting**: nodes can optimize how blocks and votes are shared across the network
-   **Strong cryptography**: BLS aggregated signatures for efficient committee voting
-   **Rigorous validation**: ongoing Rust and Haskell simulations plus formal specifications ensure correctness.

## What does Leios mean for Cardano users (eg, wallet users, DApp developers)?

For everyday users, Leios means faster transaction inclusion and a smoother experience across wallets and DApps – especially during busy periods such as airdrops or decentralized exchange (DEX) activity. For developers, it unlocks high-volume applications that were previously constrained by throughput limits. Wallets, explorers, and APIs will require updates to support the new block types (IBs, EBs, RBs), but the transition is designed to be gradual and backward-compatible where possible.

## What are the risks or trade-offs of Leios?

Leios requires modestly higher node resources (recommended: 6+ CPU cores, 100 Mbps+ bandwidth, SSD storage). The added complexity of three block types increases implementation effort, but extensive simulations and formal methods are in place to minimise risks and maintain Cardano’s high security standards.

## What are IBs, EBs, and RBs in Leios?

Leios uses three distinct block types:

-   **IB** (input block): contains raw transactions. IBs are produced frequently (up to ~5 per second) by nodes that win the IB sortition lottery.
-   **EB** (endorser block): references and endorses multiple IBs. EBs are produced every ~5 seconds by committee members.
-   **RB** (ranking block): final ranking and anchoring block produced every ~20 seconds using Praos mechanics for security and finality.
    
Each type plays a specific role: IBs collect transactions rapidly, EBs validate and endorse them in parallel, and RBs provide the secure, linear final order.

## What is the relationship between Ouroboros, Peras, and Leios?

-   **Ouroboros** is the overall family of proof-of-stake consensus protocols that powers Cardano
-   Ouroboros **Praos** is the current live protocol on mainnet
-   **Leios** is the primary scalability upgrade, significantly increasing throughput through parallel block production
-   **Peras** is the fast-finality overlay that works together with Leios to deliver both high throughput and ~2-minute high-confidence settlement.
    
Together, Leios and Peras give Cardano both massive capacity and fast user-facing confirmations while retaining Ouroboros’ proven security.

## What's the state of an IB before an EB or RB gets created for it? Is it visible, is it usable?

An input block is a signed proposal of transactions in a preliminary state. It is broadcast and visible to all nodes immediately after minting, allowing parallel validation. However, it is not yet usable – transactions cannot be spent or relied upon until endorsed by EBs and finalized by an RB. This design enables speed without sacrificing safety.

## If IBs aren’t usable until an RB is created every ~20 seconds, how does Leios actually improve performance?

Leios processes hundreds of IBs and EBs in parallel during each 20-second window. The RB is only the final security anchor, not the bottleneck. This parallelism delivers 30–65× the throughput of Praos while maintaining finality. Early endorsement from EBs also gives wallets and apps higher confidence much sooner than the full 20-second window.

## How does Leios maintain security with parallel processing?

Leios keeps Cardano’s strong security model by combining parallel processing (IBs + EBs) with a sequential finality layer (RBs). All conflicts and double-spends are resolved at the RB stage. BLS signatures and VRFs ensure only valid blocks from authorised nodes are accepted, maintaining Ouroboros’ provable security guarantees.

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

Latest simulations show only modest hardware upgrades are needed (6+ cores, 100 Mbps+ bandwidth, SSD storage). Detailed cost estimates are available in the latest simulation reports and hardware recommendation guides.

## What is the current status of Leios simulations?

Two active simulation frameworks (Rust and Haskell) continue to test network topologies, measure performance under realistic conditions, visualise block diffusion, and compare different voting/diffusion strategies.

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

- Leios documentation on this site
- [Leios development tracker](https://engineering.iog.io/leios)
- GitHub discussions in the [repository](https://github.com/input-output-hk/ouroboros-leios/discussions)
- Monthly reviews on [YouTube](https://www.youtube.com/watch?v=5uAJ-XBAysY&list=PLnPTB0CuBOBzWWpnojAK3ZaFy9RdofP6l)

These resources provide transparency and regular updates on ongoing development.

## What are the downstream effects of deploying Leios?

Leios changes how transactions are validated and how blocks and mempools operate. Wallets, explorers, indexers, and APIs will need updates to handle the new block types and higher throughput. These changes are being documented in weekly updates and technical reports.

## Is Leios production-ready?

No. Leios is in active development, with prototypes running. Testnet deployment is targeted for 2026, followed by mainnet after thorough testing, audits, and Cardano governance approval. Official updates will be published on this site and the engineering dashboard.
