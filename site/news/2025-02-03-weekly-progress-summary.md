---
title: Weekly Summary – February 3, 2025
authors:
- will
tags: [progress, update, weekly]
---

This week, the Leios team worked on cryptography benchmarking and cost calculator improvements. The team completed a reference implementation for Leios cryptography and enhanced the online cost calculator with user-requested features. They also updated both Haskell and Rust simulations to improve visualization and network modeling capabilities.

## Haskell simulation

- Added support for `Send` and `Receive` voting stages, providing:
  - A new `leios-vote-send-recv-stages` configuration option
  - A configurable stage length via `leios-stage-active-voting-slots`
- Implemented multiple diffusion strategies:
  - Added oldest-first strategy
  - Added configurable strategies for IBs, EBs, and votes via `*-diffusion-strategy`
    configurations
- Created a new `small` scenario for 100 nodes with 2,000 kB links
  - Tuned IB parameters to utilize one-third of link capacity
  - Added configurations for both `single-stage` and `send-recv` voting
- Fixed several simulation behaviors:
  - Improved block generation logic
  - Prevented duplicate EB inclusion in the base chain
  - Confirmed proper EB inclusion timing relative to vote diffusion
- The main difference observed between `single-stage` and `send-recv` is that the former
  shows a longer tail in the CPU usage CDF when the simulation is run with unlimited
  cores.

## Cryptography implementation

The Rust benchmarks for Leios cryptography were redesigned as a reference
implementation:

- Implemented the Fait Accompli sortition
- Enhanced sortition to use rational arithmetic instead of quad-precision floats
- Added Quickcheck tests for all capabilities
- Added benchmarks for serialization
- Optimized vote and certificate size.

## Cost calculator improvements

The team enhanced the
[online Leios cost calculator](https://leios.cardano-scaling.org/cost-estimator/):

- Added support for both hyperscale and discount cloud providers
- Made discount providers the default option
- Added option to amortize storage costs perpetually
- Updated defaults:
  - Single relay deployment
  - More conservative 50% disk compression
  - Perpetual storage cost amortization.

## Throughput simulator

The team updated the
[Cardano throughput simulator](https://www.insightmaker.com/insight/4DU4kmFVCFDaq30ux29PCe/Cardano-Throughput-v0-3)
with:

- The latest cloud-computing cost model
- Synchronized assumptions with an online cost calculator.

## Rust simulation

- Made minor fixes to the new graph generation strategy
- Planned out a roadmap for visualization work focusing on the Leios transaction
  lifecycle.
