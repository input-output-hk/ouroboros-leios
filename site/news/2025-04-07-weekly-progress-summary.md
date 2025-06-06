---
title: Weekly Summary – April 7, 2025
authors:
- will
tags: [progress, update, weekly, haskell-simulation, rust-simulation, workflow, optimization, analysis, workshop, edinburgh, conformance-testing]
---

This week, the team continued refining the protocol and its simulation capabilities, making significant progress in addressing various topics.

### Simulation improvements

#### Haskell simulation
- Started specifying a new relay protocol for IB header diffusion without the body
- Improved the shared log format by removing redundancies and harmonizing naming
- Added support for additional events required by conformance testing, including `SlotEvent` and `NoBlockEvent`
  - These events can be enabled using the `--conformance-events` flag with `--shared-log-format`.

#### Rust simulation
- Updated traces to match the new standardized trace format
- Fixed a critical bug in CPU scheduling where nodes were using more cores than allocated.

### Analysis of workflow optimization

The team significantly improved the workflow for analyzing both Haskell and Rust simulations:

- Replaced MongoDB with more efficient `jq` queries using map-reduce operations
- Created reusable library functions for plotting with R
- Revised and streamlined scripts for creating, executing, and analyzing simulations
- Made the Jupyter notebook for analyses more generic and reusable
- Successfully tested the new workflow on tag `leios-2025w15`.

These improvements will enable faster setup and execution of future simulation experiments, with quicker turnaround times for analysis. During this optimization work, several discrepancies between the Haskell and Rust simulations were identified and documented as GitHub issues for future investigation.

### Edinburgh workshop recaps

The Edinburgh workshop documentation has been made available, covering key discussions and decisions:

#### Day 1 highlights
- Explored ledger design options comparing labeled UTXOs (explicit shards) vs accounts (implicit shards) approaches
- Discussed conformance testing strategies including QuickCheck dynamic and trace verification approaches
- Analyzed critical edge cases for user onboarding and system properties.

#### Day 2 highlights
- Conducted a detailed analysis of Leios node costs across different TPS levels
- Key findings on resource usage:
  - At 10 TPS: 1.8x increase in egress and 6x increase in compute compared to Praos
  - At 1K TPS: significant scaling improvements with better resource efficiency
- Provided recommendations for potential integration with Peras, particularly to optimize the voting mechanism
- Discussed performance characteristics at both high and low throughput levels.

#### Day 3 highlights
- Held an in-depth discussion on optimistic ledger state references, exploring three main approaches:
  1. RB reference: highest security but highest latency
  2. EB reference: balanced approach with medium security and latency
  3. EB-DAG: advanced approach using directed acyclic graph structure
- Key advantages of the EB-DAG approach:
  - Achieves low latency while maintaining security
  - Provides strong inclusion guarantees for EBs
  - Enables efficient state management and reconstruction
  - Creates a complete, verifiable chain history
- Discussed implementation considerations for state management and block ordering under the EB-DAG model.

For more information, please see the full workshop recaps in the [Leios documentation](https://github.com/input-output-hk/ouroboros-leios/tree/main/docs/workshop).
