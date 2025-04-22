---
title: Weekly Summary - 2025-04-14
authors:
- will
tags: [progress, update, weekly]
---

This week, the team made significant progress in various areas, resulting in improved simulations, better analysis workflow, and key findings from the Edinburgh workshop.

### Simulation improvements

#### Haskell simulation
- Completed the first draft of new mini protocols for leios diffusion
  - See `simulation/docs/network-spec` for the protocol details, modeled after BlockFetch and node-to-node Tx-Submission ones from ouroboros-network.
  - IB-relay, EB-relay, Vote-relay for header diffusion and body (for IB and EB) announcements.
  - IB-fetch, EB-fetch, for body diffusion.
  - CatchUp protocol for older blocks.
- Renamed `short-leios` command to `leios` since it covers full variant too.
  - `short-leios` is kept as alias for compatibility.

#### Rust simulation
- Fixed conformance with shared trace format
- Fixed bug with voting logic which was preventing EBs from receiving enough votes to get on-chain
- Updated visualization to use smaller trace files, to prepare for hosting on docs site

### Revisions to cost dashboard

The [cost dashboard](https://leios.cardano-scaling.org/cost-estimator/) was updated with lower and more realistic IO estimates.

### Analysis of transaction lifecycle

The Jupyter notebook [Analysis of transaction lifecycle](analysis/tx-to-block.ipynb) estimates the delay imposed by each of the seven stages of Full Leios as a transaction moves from memory pool to being referenced by a Praos block.

The plot hints at the following:
1. There seems little advantage to moving to stage lengths less than 10 slots.
2. The number of shards should be kept small enough so that the IB rate per shard is high relative to the stage length.
3. Low EB rates result in many orphaned IBs.
4. Realistic parameter settings result in an approximately two-minute delay between transaction submission and its referencing by an RB.

Potential next steps:
- Translating this model into Delta QSD, so that network effects can be included.
- Compare this model's results to output of the Rust simulator.
- Elaborate the model in order to represent the memory-pool and ledger variants under consideration.

## Key findings from Edinburgh workshop recaps

Key discussions, decisions, and findings include:
- Labeled UTXOs (explicit shards) vs accounts (implicit shards) approaches for ledger design.
- Conformance testing strategies including QuickCheck dynamic and trace verification approaches.
- Critical edge cases for user onboarding and system properties.

The team conducted a detailed analysis of Leios node costs across different TPS levels. Key findings include:
- At 10 TPS: 1.8x increase in egress and 6x increase in compute compared to Praos
- At 1K TPS: significant scaling improvements with better resource efficiency.

Recommendations for potential integration with Peras include optimizing the voting mechanism.

The team also discussed performance characteristics at both high and low throughput levels, held an in-depth discussion on optimistic ledger state references, and explored the potential of EB-DAG approach for achieving low latency while maintaining security.

## Detailed Edinburgh workshop highlights

The detailed Edinburgh workshop recaps have been made available, covering key discussions, decisions, and findings.

### Day 1 highlights
- Explored ledger design options comparing labeled UTXOs (explicit shards) vs accounts (implicit shards) approaches
- Discussed conformance testing strategies including QuickCheck dynamic and trace verification approaches
- Analyzed critical edge cases for user onboarding and system properties.

### Day 2 highlights
- Conducted a detailed analysis of Leios node costs across different TPS levels
- Key findings on resource usage include:
  - At 10 TPS: 1.8x increase in egress and 6x increase in compute compared to Praos
  - At 1K TPS: significant scaling improvements with better resource efficiency
- Provided recommendations for potential integration with Peras, particularly to optimize the voting mechanism
- Discussed performance characteristics at both high and low throughput levels

### Day 3 highlights
- Held an in-depth discussion on optimistic ledger state references
- Explored three main approaches:
  1. RB reference: highest security but highest latency
  2. EB reference: balanced approach with medium security and latency
  3. EB-DAG: advanced approach using directed acyclic graph structure
- Key advantages of the EB-DAG approach:
  - Achieves low latency while maintaining security
  - Provides strong inclusion guarantees for EBs
  - Enables efficient state management and reconstruction
  - Creates a complete, verifiable chain history
- Discussed implementation considerations for state management and block ordering under the EB-DAG model

For more information, please see the full workshop recaps in the [Leios documentation](https://github.com/input-output-hk/ouroboros-leios/tree/main/docs/workshop).
