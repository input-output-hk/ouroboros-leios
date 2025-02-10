---
title: Weekly progress summary – February 3, 2025
authors:
- will
tags: [progress, update, weekly]
---

## High-level summary

This week saw significant progress in cryptography benchmarking and cost
calculator improvements. The team completed a reference implementation for Leios
cryptography and enhanced the online cost calculator with user-requested
features. Both Haskell and Rust simulations received updates to improve
visualization and network modeling capabilities.

## Haskell simulation

- Added support for Send and Receive Voting stages
  - New configuration option `leios-vote-send-recv-stages`
  - Configurable stage length via `leios-stage-active-voting-slots`
- Implemented multiple diffusion strategies:
  - Added oldest-first strategy
  - Configurable strategies for IBs, EBs, and votes via `*-diffusion-strategy`
    configs
- Created new `small` scenario for 100 nodes with 2000kBs links
  - Tuned IB parameters to utilize one-third of link capacity
  - Configurations for both single-stage and send-recv voting
- Fixed several simulation behaviors:
  - Improved block generation logic
  - Prevented duplicate EB inclusion in base chain
  - Confirmed proper EB inclusion timing relative to vote diffusion
- Main difference observed between single-stage and send-recv is the former
  shows a longer tail in the CPU usage CDF when simulation is run with unlimited
  cores

## Cryptography implementation

The Rust benchmarks for Leios cryptography were redesigned as a reference
implementation:

- Implemented the Fait Accompli sortition
- Enhanced sortition to use rational arithmetic instead of quad-precision floats
- Added Quickcheck tests for all capabilities
- Added benchmarks for serialization
- Optimized vote and certificate size

## Cost calculator improvements

The
[online Leios cost calculator](https://leios.cardano-scaling.org/cost-estimator/)
received several enhancements:

- Added support for both hyperscale and discount cloud providers
- Made discount providers the default option
- Added option to amortize storage costs perpetually
- Updated defaults:
  - Single relay deployment
  - More conservative 50% disk compression
  - Perpetual storage cost amortization

## Throughput simulator

Updated the
[Cardano throughput simulator](https://www.insightmaker.com/insight/4DU4kmFVCFDaq30ux29PCe/Cardano-Throughput-v0-3)
with:

- Latest cloud-computing cost model
- Synchronized assumptions with online cost calculator

## Rust simulation

- Minor fixes to new graph generation strategy
- Planned out a roadmap for visualization work focusing on Leios transaction
  lifecycle
