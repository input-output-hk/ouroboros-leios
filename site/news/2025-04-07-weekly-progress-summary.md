---
title: Weekly Summary - April 7, 2025
authors:
- will
tags: [progress, update, weekly]
---

This week, the team continued their efforts in refining the protocol and its simulation capabilities. The team made significant progress in addressing various topics.

### Simulation improvements

#### Haskell simulation
- Started specification of a new relay protocol for IB header diffusion without body
- Improved the shared log format by removing redundancies and harmonizing naming
- Added support for extra events required by conformance testing, including `SlotEvent` and `NoBlockEvent`
  - These events can be enabled using the `--conformance-events` flag with `--shared-log-format`.

#### Rust simulation
- Updated traces to match the new standardized trace format
- Fixed a critical bug related to CPU scheduling where nodes were using more cores than allocated.

### Analysis workflow optimization

The team significantly improved the workflow for analyzing both Haskell and Rust simulations:

- Replaced MongoDB with more efficient `jq` queries using map-reduce operations
- Created reusable library functions for plotting with R
- Revised and streamlined scripts for creating, executing, and analyzing simulations
- Made the Jupyter notebook for analyses more generic and reusable
- Successfully tested the new workflow on tag `leios-2025w15`

These improvements will enable faster setup and execution of future simulation experiments, with quicker turnaround times for analysis. During this optimization work, several discrepancies between the Haskell and Rust simulations were identified and documented as GitHub issues for future investigation.

### Edinburgh Workshop Recaps

The Edinburgh Workshop documentation has been made available, covering key discussions and decisions:

#### Day 1 Highlights
- Explored ledger design options comparing Labeled UTxOs (Explicit Shards) vs Accounts (Implicit Shards) approaches
- Discussed conformance testing strategies including QuickCheck Dynamic and Trace Verification approaches
- Analyzed critical edge cases for user onboarding and system properties

#### Day 2 Highlights
- Detailed analysis of Leios node costs at different TPS levels
- Key findings on resource usage:
  - At 10 TPS: 1.8x increase in egress and 6x increase in compute compared to Praos
  - At 1K TPS: Significant scaling improvements with better resource efficiency
- Recommendations for potential integration with Peras, particularly for voting mechanism optimization
- Discussion of performance characteristics at both high and low throughput levels

#### Day 3 Highlights
- In-depth discussion of optimistic ledger state references, exploring three main approaches:
  1. RB Reference: Highest security but highest latency
  2. EB Reference: Balanced approach with medium security and latency
  3. EB-DAG: Advanced approach using directed acyclic graph structure
- Key advantages of the EB-DAG approach:
  - Achieves low latency while maintaining security
  - Provides strong inclusion guarantees for EBs
  - Enables efficient state management and reconstruction
  - Creates complete, verifiable chain history
- Implementation considerations for state management and block ordering in the EB-DAG approach

For detailed information, see the full workshop recaps in the [Leios documentation](https://github.com/input-output-hk/ouroboros-leios/tree/main/docs/workshop).