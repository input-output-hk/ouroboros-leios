---
title: Weekly Summary – February 17, 2025
authors:
- will
tags: [progress, update, weekly]
---

## High-level summary

This week in Leios development, [CPS-0018](https://github.com/cardano-foundation/CIPs/blob/master/CPS-0018/README.md) for transaction throughput was approved, along with improved Docker support for simulations and analysis of cross-simulation results. The team also examined input block (IB) production rates and their impact on network performance.

## Protocol development

- CPS-0018 'Greater transaction throughput' officially approved:
  - Merged into Cardano Foundation's CIP/CPS repository
  - Documents urgency of higher transaction throughput
  - Defines goals for the Leios initiative
  - Identifies key open questions and use cases.

## Cross-simulation analysis

- Conducted a comprehensive [analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/Logbook.md#simulation-of-varied-ib-production-rate) of IB production rates ranging from 1 IB/s to 100 IB/s:
  - Developed an ELT workflow for data processing via MongoDB
  - Created an R Jupyter notebook for analysis and visualization
  - Identified and addressed three significant bugs ([#207](https://github.com/input-output-hk/ouroboros-leios/issues/207), [#208](https://github.com/input-output-hk/ouroboros-leios/issues/208), [#209](https://github.com/input-output-hk/ouroboros-leios/issues/209))
- Key findings from the Haskell simulation:
  - Network congestion emerges at high IB production rates
  - Both average propagation time and slow propagation tail increase
  - A critical threshold of ~40 IBs/s was identified, beyond which network congestion severely impacts block reception
- Comparison of PeerNet and Haskell simulations:
  - Both exhibit qualitatively similar block propagation distributions
  - Both demonstrate protocol breakdown under high block production rates
  - Differences in resolution and configuration prevent exact comparison.

## Infrastructure improvements

- Added comprehensive Docker support for both simulations:
  - Optimized multi-stage Docker files for Haskell and Rust
  - Simplified deployment process
  - Enabled easy configuration via volume mounts and parameters
  - Documented usage in README.md.

## Rust simulation

- Enhanced Rust simulation capabilities:
  - Implemented bandwidth usage tracking
  - Added configurable bandwidth limits per connection
  - Fixed issues identified in cross-simulation comparisons
  - Started updating visualizations for improved clarity.

## Haskell simulation

- Enhanced IB sortition handling for IB/slot < 1
- Began integrating block expiration and diffusion-halt proposal
- Implemented ideal timing calculations for diffusion:
  - Added uniform block behavior configuration
  - Identified relay mini-protocol complexities:
    - Variable latency (3-4) for block transfer
    - Latency depends on traffic conditions and request handling.

## Formal methods

- Moved formal specification to a [dedicated repository](https://github.com/input-output-hk/ouroboros-leios-formal-spec)
- Established a conformance testing framework:
  - Enabled testing between Short Leios implementations
  - Documented the test suite execution process
- Initiated a survey of network models across IO consensus projects. 
