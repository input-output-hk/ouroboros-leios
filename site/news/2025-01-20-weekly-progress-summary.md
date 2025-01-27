---
title: Weekly progress summary – January 20, 2025
authors:
- will
tags: [progress, update, weekly]
---

## Simulation Progress

### Haskell Implementation

- Enhanced parameter handling with support for reading configurations and
  topologies from disk
- Added new `generate-topology` command for random topology generation
- Aligned Leios sortition with algorithms from sortition benchmarks and
  technical report
- Completed analysis comparing Praos simulation with benchmark cluster
  - Adoption times within 10% of measured values
  - Review of simulation parameters pending
- Next steps identified:
  - Generate topologies with block producers behind relays
  - Begin comparison with idealized diffusion model
  - Configure and run simulations for higher throughput

### Rust Implementation

- Completed first pass of block-level visualization
- Updated topology files to include baked-in latencies
- Improved output with human-readable names from shared topology format
- Enhanced simulation output comparability across different simulations

## Analysis & Research

### Sortition Analysis

- Completed detailed analysis of "Fiat Accompli" sortition scheme using mainnet
  stake distribution (Epoch 535)
- Key findings for 500-vote committees:
  - 406 largest stake block-producers would be deterministic voters
  - ~88 voters would be randomly selected
  - Significant certificate size reduction achieved through deterministic voter
    selection

### Downstream Impact Assessment

Started comprehensive analysis of Leios's ecosystem impact:

- Identified impacts on indexers, explorers, SDKs, and APIs due to ledger and
  node changes
- Transaction construction and memory-pool sharding effects on dapps and wallets
- Physical layer visibility considerations for sophisticated use cases
- High throughput implications for event filtering efficiency
- Transaction journey time considerations from memory pool to Praos block
  reference

### DeltaQ Analysis

- Successfully matched ΔQ model for IB diffusion across both simulation
  implementations
- Identified key differences in simulation approaches:
  - Haskell simulation includes bandwidth effects (328ms network delay per hop
    at 1MB/s)
  - Rust simulation currently excludes bandwidth effects
- Enabled cross-simulation topology sharing for consistent testing
