---
title: Weekly Summary – June 17, 2025
authors:
- will
tags: [progress, update, weekly, bandwidth, experiments, throughput, analysis, simulation, formal-methods, cddl, specifications]
---

This week, the Leios team conducted extensive experiments using the previously developed network topologies to study transaction and input block throughput limits under realistic conditions. The team also conducted empirical bandwidth measurements between data centers, advanced formal methods capabilities, and created initial CDDL specifications for core Leios components.

## CDDL specification draft

- Created initial CDDL specifications for core Leios components:
  - Input blocks with VRF lottery and single IB/slot limits
  - Endorser blocks as a new aggregation block type
  - Ranking blocks as Conway extension with optional certificates
  - BLS voting system with persistent/non-persistent voters and key registration
- Followed crypto-benchmarks implementation approach while maintaining Conway CDDL compatibility
- Established foundational structures in the first draft covering common base components
- Future iterations will add detailed specifications for design variants, including full sharding, overcollateralization, and protocol extensions.

## Formal methods

- Added support for `Late IB inclusion` to the formal specification of Full-Short Leios
- Profiled leios-trace-verifier performance, identifying that approximately 60% of execution time is spent in garbage collection
- Improved performance significantly by switching to `--nonmoving-gc` garbage collection strategy.

## Bandwidth measurements

- Conducted empirical bandwidth measurements using `iperf3` between data centers in North America and Europe
- Measured bidirectional connections across multiple cloud providers (OVH, AWS, CenturyLink)
- Results ranged from 95 Mbps to 973 Mbps, depending on geographic distance and the provider
- Identified 100 Mbps as a conservative lower bound for inter-datacenter connections
- Observed 5-20% reduction in individual link speeds when multiple simultaneous connections are active.

## Large-scale network experiments

- Conducted comprehensive experiments using both the 750-node and 10,000-node network topologies with Haskell and Rust simulations
- Studied transaction and IB throughput limits for realistic scenarios up to 300 TPS and 32 IB/s
- Key findings from the 750-node mini-mainnet experiments are documented in [analysis results](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w24/analysis.ipynb) and [summary slides](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w24/summary.pdf):
  - The 750-node mini-mainnet serves as a suitable replacement for the 10,000-node pseudo mainnet for performance measurements
  - Substantial agreement between Haskell and Rust simulations for mini-mainnet scenarios
  - Block propagation times under one second, consistent with empirical observations from pooltool.io
  - Protocol can support 25 MB/s throughput with 1 Gb/s links before degradation
  - Mean transaction time from mempool to ledger is approximately 150 seconds
  - Achieved 80% disk-space efficiency with ~20% network traffic overhead
  - Six-core VM is sufficient for peak demand at 300 TPS, with average demand under two cores
- Results from 10,000-node pseudo-mainnet experiments are available in [analysis documentation](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w23/analysis.ipynb) and [presentation slides](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w23/summary.pdf):
  - Average transaction lifecycle of 100 seconds from mempool to ledger
  - Approximately 80% efficiency for both disk and network usage
  - Six CPU cores are sufficient for peak load handling even at high TPS rates
  - Block propagation time averaged under one second across the large network.
