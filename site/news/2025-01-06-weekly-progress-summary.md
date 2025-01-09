---
title: Weekly Progress Summary - January 6, 2025
authors:
- will
tags: [progress, update]
---

## Rust Simulation

- Added basic simulation of CPU usage/latency.
- Implemented "lottery won" events to identify the start of CPU processing.
- Each node has 4 simulated cores, configurable per-node.
- TX validation and RB/IB/EB generation/validation each take one CPU task.
- All vCPU costs were copied from the cost estimator.

## DeltaQ Summary Update

- Added MIN / MAX combinators for best- and worst-case simulation results.
- Rust simulation best case does not match analytically best behavior.
- Haskell simulation best case is too fast; ΔQ expression must assume >200 peers
  per node.

## Cost Dashboard Updates

- Improved input parameters and computations.
- Lengthened phases and reduced EB rate.
- Updated CPU costs for votes and certificates.
- Revised IOPS values based on empirical data from Cardano nodes.

## Benchmarking BLS Signatures

- Benchmarked BLS votes using the Rust bls-signatures package.
- Aggregate verification significantly speeds up the process.
- Provided CPU time estimates for various operations.

## Votes and Certificates

- Updated size estimates for votes.
- Added CPU time estimates for BLS votes and certificates.
- Drafted technical report sections on BLS and MUSEN certificates.

## Sortition Analysis

- Analyzed sortition for IBs, EBs, and votes.
- Added findings to the draft of the first technical report.
