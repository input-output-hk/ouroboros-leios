---
title: Weekly progress summary – February 10, 2025
authors:
- will
tags: [progress, update, weekly]
---

## High-level summary

This week, the Leios team made significant progress across multiple areas. Major developments included detailed DeltaQ analysis of network topologies, extensive BLS cryptography benchmarking, and improvements to both simulations. The team also explored succinct schemes for BLS key registration and conducted detailed certificate performance analysis. Both Haskell and Rust simulations received substantial updates to improve visualization and support more realistic testing conditions.

## DeltaQ analysis

- Enhanced the `topology-checker` with ΔQSD analysis capabilities:
  - Extracts inter-node latencies from given topologies
  - Classifies latencies into near/far components
  - Builds parameterized ΔQ models
  - Outputs fitted models in `delta_q` web app syntax
- Key findings from topology analysis:
  - Clear distinction between near/far components in examined topologies
  - Unexpectedly high hop counts in latency-weighted Dijkstra paths
    - Mean 4-5, max 8 for topology-100
    - Min 8, max 20 for "realistic" topology
  - Model fitting achieved rough shape matching but showed significant deviations at low latencies
  - Resource usage tracking goals remain unachieved due to complexity in understanding load multiplication factors

## BLS cryptography

- Completed comprehensive benchmarking of certificate operations:
  - Detailed performance analysis across committee sizes (500-1000 seats)
  - Certificate generation: 63.4ms - 92.5ms
  - Certificate verification: 104.8ms - 144.9ms
  - Certificate weighing: ~12ms consistently
- Explored succinct schemes for key registration:
  - Proposed 90-day key evolution with 124-byte KZG commitments
  - Analyzed message sizes for key opening (316 bytes per pool)
  - Investigated SNARK-based alternatives for proof of possession
- Added BLS crypto to CI pipeline with automated testing
- Documented parallelization strategies for certificate operations

## Formal methods

- Added conformance testing client for the executable Short Leios specification
- Successfully merged the executable specification for Simplified Leios into main

## Haskell simulation

- Updated configuration defaults for block sizes and timings
- Added support for idealized simulation conditions:
  - Single-peer block body requests
  - TCP congestion window modeling
  - Mini-protocol multiplexing
  - Unlimited bandwidth links support
- Enhanced simulation output and analysis:
  - Added raw field for accumulated data
  - Implemented block diffusion CDF extraction
  - Created multi-CDF plotting capabilities

## Rust simulation

- Enhanced visualization capabilities:
  - Added block size breakdown display
  - Implemented total bytes sent/received tracking
  - Added total TX count and CPU time metrics
- Improved event handling:
  - Updated to standard timestamp format (seconds)
  - Enhanced CPU task event structure
  - Added CBOR output support
- Added support for multiple strategies:
  - Implemented `ib-diffusion-strategy` (freshest-first, oldest-first, peer-order)
  - Added `relay-strategy` affecting TXs, IBs, EBs, votes, and RBs
  - Enabled unlimited EB and vote bundle downloads from peers 