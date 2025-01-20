---
title: Weekly progress summary – January 13, 2025
authors:
- will
tags: [progress, update, weekly]
---

## Cryptography Benchmarks

- Implemented and benchmarked complete Leios cryptography suite in the
  `leios_crypto_benchmarks` Rust crate
- Key VRF performance metrics:
  - Proving: 240 µs
  - Verifying: 390 µs
- Sortition performance (excluding VRF):
  - Leadership checks (RB/IB/EB): 0.17 µs per slot/pipeline
  - Vote number calculation: 3.8 µs per pipeline
- BLS operations benchmarked:
  - Key possession proof verification: 1.5 ms per key
  - Vote generation/verification: 280 µs / 1.4 ms per vote
  - Certificate operations (300-vote quorum): 50 ms generation, 90 ms
    verification

## Cryptography Design Progress

- Optimized vote signature size to potentially as small as 192 bytes
- Determined that 500-vote committee certificates (60% quorum) would fit within
  Praos blocks at ~58 kB
- Explored potential synergies with KES rotation and Praos VRF BLS keys
- Completed cryptography sections for first technical report
- Decision made to freeze current report content and move new findings to future
  documents

## Simulation Development

### Haskell Simulation

- Achieved diffusion latency comparable to benchmark cluster data for Praos
  blocks
- Integrated agreed-upon simulation parameters with Rust team
- Added event log output functionality with JSON support
- Implemented 'short-leios' simulation variant matching mainnet ranking block
  interval
- Fixed coordination issues in Relay mini-protocol consumers
- Completed PI goal by adding total data transmitted per node visualization

### Rust Simulation

- Implemented more granular CPU simulation times
- Fixed race condition in simulated clock
- Started consuming new shared configuration file format
- Established shared configuration format with default parameters in
  `data/simulation/default.yaml`
