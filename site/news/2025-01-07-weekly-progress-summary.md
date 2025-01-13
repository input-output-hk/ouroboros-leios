---
title: Weekly Progress Summary - January 7, 2025
authors:
- will
tags: [progress, update, weekly]
---

## Rust Simulation

- Simulated infinite CPUs and output CPU events in logs.

- Enhancements:
  - Added basic simulation of CPU usage/latency.
  - Introduced "lottery won" events to identify the start of CPU processing.
  - Configured each node with 4 simulated cores for CPU-bound tasks.
  - TX validation and RB/IB/EB generation/validation each take one CPU task.
  - All vCPU costs were copied from the cost estimator.

## DeltaQ

- Added MIN / MAX combinators for best- and worst-case simulation results.
- Rust simulation best case does not match analytically best behavior.
- Haskell simulation best case is too fast; ΔQ expression must assume >200 peers
  per node.
- Concluded that this work stream has failed due to discrepancies in simulation
  results.

## Summary of Dec 17 Q&A Discussion

- Discussed throughput dashboard and its potential as a formal website.
- Explored the impact of Leios on ledger changes, data structures, and
  ecosystem.
- Considered using Mithril for proofs of equivocation.
- Discussed elasticity and adaptability of nodes.
- Explored interactions between emerging hydra protocols and L1.

## Cost Dashboard Updates

- Updated dashboard with improved parameters and computations:
  - Lengthened phases and reduced EB rate based on technical report analysis
  - Revised CPU costs for votes and certificates per technical report
  - Updated IOPS values using empirical Cardano node production data
  - Aligned Agda code with web interface and cross-validated
  - Future updates pending calibration data from Haskell/Rust simulations
