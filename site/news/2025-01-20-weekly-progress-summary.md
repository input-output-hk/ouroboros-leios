---
title: Weekly progress summary – January 20, 2025
authors:
- will
tags: [progress, update, weekly]
---

## Simulation progress

### Haskell implementation

- Enhanced parameter handling with support for reading configurations and
  topologies from disk
- Added a new `generate-topology` command for random topology generation
- Aligned Leios sortition with algorithms from sortition benchmarks and the
  technical report
- Completed analysis comparing the Praos simulation with the benchmark cluster
  - Adoption times within 10% of measured values
  - Review of simulation parameters pending
- Next steps identified:
  - Generate topologies with block producers behind relays
  - Begin comparison with the idealized diffusion model
  - Configure and run simulations for higher throughput.

### Rust implementation

- Completed the first pass of block-level visualization
- Updated topology files to include baked-in latencies
- Improved output with human-readable names from the shared topology format
- Enhanced simulation output comparability across different simulations.

## Analysis and research

### Sortition analysis

- Completed a detailed analysis of the 'Fiat Accompli' sortition scheme using mainnet
  stake distribution (Epoch 535)
- Key findings for 500-vote committees:
  - 406 largest stake block-producers would be deterministic voters
  - ~88 voters would be randomly selected
  - Significant certificate size reduction achieved through deterministic voter
    selection.

### Downstream impact assessment

Started comprehensive analysis of Leios's impact on the ecosystem:

- Identified impacts on indexers, explorers, SDKs, and APIs resulting from ledger and
  node changes
- Transaction construction and memory-pool sharding effects on DApps and wallets
- Physical layer visibility considerations for sophisticated use cases
- High throughput implications for event filtering efficiency
- Transaction journey time considerations from memory pool to Praos block
  reference.

### DeltaQ analysis

- Successfully matched ΔQ model for IB diffusion across both simulations and
  implementations
- Identified key differences in simulation approaches:
  - Haskell simulation includes bandwidth effects (328ms network delay per hop
    at 1MB/s)
  - Rust simulation currently excludes bandwidth effects
- Enabled cross-simulation topology sharing for consistent testing.
