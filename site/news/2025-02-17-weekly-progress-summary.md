---
title: Weekly progress summary – February 17, 2025
authors:
- will
tags: [progress, update, weekly]
---

## High-level summary

This week marked significant progress in multiple areas of the Leios project. Major developments included the approval of [CPS-0018](https://github.com/cardano-foundation/CIPs/blob/master/CPS-0018/README.md) for transaction throughput, enhanced Docker support for simulations, and important findings from cross-simulation comparisons. The team also made strides in analyzing IB production rates and their impact on network performance.


## Protocol development

- [CPS-0018](https://github.com/cardano-foundation/CIPs/blob/master/CPS-0018/README.md) "Greater Transaction Throughput" officially approved:
  - Merged into Cardano Foundation's CIP/CPS repository
  - Documents urgency of higher transaction throughput
  - Defines goals for Leios initiative
  - Identifies key open questions and use cases


## Cross-simulation analysis

- Conducted comprehensive [analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/Logbook.md#simulation-of-varied-ib-production-rate) of IB production rates from 1 IB/s to 100 IB/s:
  - Developed ELT workflow for data processing via MongoDB
  - Created R Jupyter notebook for analysis and visualization
  - Identified and addressed three significant bugs ([#207](https://github.com/input-output-hk/ouroboros-leios/issues/207), [#208](https://github.com/input-output-hk/ouroboros-leios/issues/208), [#209](https://github.com/input-output-hk/ouroboros-leios/issues/209))
- Key findings from Haskell simulation:
  - Network congestion emerges at high IB production rates
  - Both average propagation time and slow propagation tail increase
  - Critical threshold identified at ~40 IBs/s where network congestion severely impacts block reception
- Compared PeerNet and Haskell simulations:
  - Qualitatively similar block propagation distributions
  - Both demonstrate protocol breakdown under high block production rates
  - Differences in resolution and configuration prevent exact comparison

## Infrastructure improvements

- Added comprehensive Docker support for both simulations:
  - Multi-stage Dockerfile optimization for both Haskell and Rust
  - Simplified deployment process
  - Easy configuration via volume mounts and parameters
  - Documented usage in README.md

## Rust simulation

- Enhanced Rust simulation capabilities:
  - Implemented bandwidth usage tracking
  - Added configurable bandwidth limits per connection
  - Fixed issues discovered during cross-simulation comparison
  - Started professional visualization updates

## Haskell simulation

- Enhanced IB sortition handling for IB/slot < 1
- Began integration of block expiration/diffusion-halt proposal
- Implemented ideal timing calculations for diffusion:
  - Added uniform block behavior configuration
  - Identified Relay mini-protocol complexity:
    - Variable latency (3-4) for block transfer
    - Dependent on traffic conditions and request handling method

## Formal methods

- Relocated formal specification to [dedicated repository](https://github.com/input-output-hk/ouroboros-leios-formal-spec)
- Established conformance testing framework:
  - Enabled testing between Short Leios implementations
  - Documented test suite execution process
- Initiated survey of network models across IO consensus projects 