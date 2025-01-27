---
title: Weekly progress summary – January 20, 2025
authors:
- will
tags: [progress, update, weekly]
---

## Simulation Improvements

### Haskell Implementation

- Enhanced parameter handling with support for reading configurations and
  topologies from disk
- Added new `generate-topology` command for random topology generation
- Aligned Leios sortition with algorithms from sortition benchmarks and
  technical report
- Completed analysis comparing Praos simulation with benchmark cluster
  - Adoption times within 10% of measured values
  - Review of simulation parameters pending

### Rust Implementation

- Implemented block-level visualization to complement existing graph view
- Updated topology files to include baked-in latencies
- Improved output with human-readable names from shared topology format
- Enhanced simulation output comparability across different simulations

## Analysis & Research

### Sortition Analysis

- Completed analysis of "Fiat Accompli" sortition scheme using mainnet stake
  distribution
- Key findings for 500-vote committees:
  - 406 largest stake block-producers would be deterministic voters
  - ~88 voters would be randomly selected
  - Significant certificate size reduction achieved through deterministic voter
    selection

### Downstream Impact Assessment

- Initiated comprehensive analysis of Leios's ecosystem impact
- Key areas identified:
  - Ledger and node data structure changes affecting indexers and explorers
  - Transaction construction impacts on dapps and wallets
  - Physical layer querying requirements for sophisticated use cases
  - Event filtering optimization needs for high throughput scenarios

### DeltaQ Analysis

- Successfully matched ΔQ model for IB diffusion across both simulation
  implementations
- Identified key differences in simulation approaches:
  - Haskell simulation includes bandwidth effects (328ms network delay per hop
    at 1MB/s)
  - Rust simulation currently excludes bandwidth effects
- Completed new comparisons using JSONL event logs
- Investigating diffusion timing differences between implementations

## Cryptography Performance

- Completed comprehensive benchmarking of the Leios cryptography suite
- Notable performance achievements:
  - VRF operations: 240 µs for proving, 390 µs for verification
  - Leadership checks efficiency: 0.17 µs per slot/pipeline
  - Vote processing: 3.8 µs per pipeline calculation
  - BLS operations: 1.5 ms for key verification, vote operations ranging 280 µs
    to 1.4 ms

## Design Optimizations

- Successfully optimized vote signature size down to 192 bytes
- Validated committee certificates (500 votes, 60% quorum) compatibility with
  Praos blocks at ~58 kB
- Explored integration possibilities with KES rotation and Praos VRF BLS keys
- Finalized initial technical report cryptography sections

## Simulation Progress

### Multi-Platform Development

- Haskell Implementation:
  - Achieved target diffusion latency matching benchmark cluster data
  - Added JSON-based event logging
  - Implemented 'short-leios' variant for mainnet ranking
  - Enhanced visualization for per-node data transmission

- Rust Implementation:
  - Improved CPU simulation granularity
  - Resolved clock simulation race conditions
  - Implemented shared configuration system with standardized parameter files
  - Established default simulation parameters in YAML format
