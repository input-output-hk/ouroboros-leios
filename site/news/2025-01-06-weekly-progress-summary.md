---
title: Weekly Summary – January 6, 2025
authors:
- will
tags: [progress, update, weekly]
---

## Rust simulation

- Added a basic simulation of central processing unit (CPU) usage/latency
- Implemented 'lottery won' events to identify the start of CPU processing
- Configured each node with four simulated cores, adjustable per node
- Transaction validation and ranking block/input block/endorser block generation/validation each take one CPU task
- All virtual CPU costs were copied from the cost estimator.

## DeltaQ summary update

- Added MIN/MAX combinators for best- and worst-case simulation results
- The Rust simulation best case does not match the analytically best behavior
- The Haskell simulation best case is too fast; the ΔQ expression must assume more than 200 peers per node.

## Cost dashboard updates

- Improved input parameters and computations
- Lengthened phases and reduced endorser block rate
- Updated CPU costs for votes and certificates
- Revised input/output operations per second (IOPS) values based on empirical data from Cardano nodes.

## Benchmarking BLS signatures

- Benchmarked BLS votes using the Rust `bls-signatures` package
- Aggregate verification significantly speeds up the process
- Provided CPU time estimates for various operations.

## Votes and certificates

- Updated size estimates for votes
- Added CPU time estimates for BLS votes and certificates
- Drafted technical report sections on BLS and MUSEN certificates.

## Sortition analysis

- Analyzed sortition for input and endorser blocks and votes
- Added findings to the draft of the first technical report.
