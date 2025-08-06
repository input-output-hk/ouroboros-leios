---
title: Weekly Summary – July 21, 2025
authors:
- will
tags: [progress, update, weekly, cip-development, throughput-metrics, validation-analysis, high-throughput-validation, simulation-documentation]
---

This week, the Leios team made significant progress on CIP development, refined validation timing analysis with improved methodologies, and achieved high-throughput validation milestones. The team completed major components of the CIP specification, proposed improved throughput metrics for better comparability, and demonstrated a 1,000 TPS capability with specific protocol variants.

## CIP development progress

### Protocol specification completion

- Completed a comprehensive review of the protocol overview, component flow, and parameters
- Integrated vote and certificate specifications into the CIP documentation
- Drafted node behavior and network specifications, including mini-protocol definitions
- Progressed the CIP towards completion, with all core protocol components now fully specified.

## Throughput metrics standardization

### Improved measurement methodology

- Proposed transition from transaction-per-second (Tx/s) to transaction-bytes-per-second (TxB/s) metrics for enhanced comparability
- Recommended using Tx/s only in introductory statements with transaction size context (eg, '100 Tx/s with 1,400 B transactions')
- Established TxkB/s and TxMB/s as primary throughput metrics for analysis
- Benefits include:
  - Direct comparability across different transaction sizes
  - Clear nominal storage and network demand calculations
  - Example: 100 Tx/s with 1,400 B transactions = 140 TxkB/s = ~12 GB/day storage
  - Network overhead calculation: 140 TxkB/s × 10 peers = 11.2 Mb/s.

## Enhanced validation analysis

### Revised Cardano validation timing study

- Completed a refined analysis of Cardano mainnet validation times using a clean dataset on an idle machine
- Significantly improved accuracy over preliminary results by eliminating CPU contention effects
- Updated findings for transaction signature verification and Plutus script execution:
  - Median times: 428.4 μs/tx and 211.5 μs/kB
  - Linear model: 148.1 μs/tx plus 114.1 μs/kB
  - Enhanced model: 137.5 μs/tx plus 60.2 μs/kB plus 585.2 μs/Gstep with Laplace error distribution
- Results are suitable for bulk block estimates despite individual transaction prediction limitations
- Findings support reducing CPU-timing parameters in default Leios simulation configurations
- A comprehensive analysis is available in the [validation timing documentation](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/timings/ReadMe.ipynb).

## High-throughput protocol validation

### 1,000 TPS Linear Leios demonstration

- Successfully demonstrated Linear Leios with transaction references supporting 1,000 tx/s at 300 B/tx
- Validated Stracciatella variant capability at 1,000 TPS throughput levels
- Confirmed that Linear Leios with embedded transactions cannot sustain such throughput
- Results provide clear protocol variant performance boundaries for high-throughput scenarios
- Detailed evidence and analysis are available in the [1,000 TPS study notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w30/analysis.ipynb).

## Simulation infrastructure improvements

### Rust simulation documentation

- Enhanced the documentation of the current Rust simulation implementation
- Documented available protocol variants and their implementation status
- Improved accessibility and usability of the simulation framework for protocol development.

## Next steps

- Finalize CIP documentation for community review and feedback
- Implement standardized throughput metrics across analysis frameworks
- Apply revised validation timing parameters to simulation configurations
- Expand high-throughput testing to additional protocol variants and scenarios.
