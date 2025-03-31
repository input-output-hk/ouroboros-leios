---
title: Weekly Summary – March 24, 2025
authors:
- will
tags: [progress, update, weekly]
---

This week, the Leios team continued working on various aspects of the protocol and its simulation capabilities. They made progress in implementing and testing the Haskell and Rust simulators, focusing on protocol behavior under different network conditions.

## Simulation progress

- **Haskell simulation**
  - Moved configuration and topology parsers to the `leios-trace-hs` package for reuse in formal methods
  - Investigated differences in IBs referenced with Rust simulation: identified that inconsistencies were caused by the same sequence of random samples being used across different runs
  - Simplified sortition code by using an external statistics package
  - Tested Full Leios, resolving tension between `r_EB`/`eb-max-age-slots` and `praos-chain-quality`/`η`
  - Fixed `cabal run ols -- generate-topology close-and-random`, listing `producers` properly and decreasing variance in upstream peers.

- **Rust simulation**
  - Investigated anomalies in simulation results: identified that earlier IB production failures were caused by low connectivity and lower CPU usage compared to the Haskell simulation
  - Refined Full Leios implementation
  - Added Full Leios support to the visualizer
  - Migrated the visualizer from Next.js to Vite.

## Analysis of simulations

- **Tag `leios-2025w13`:** simulated 198 Short Leios scenarios, varying IB production rate, IB size, network topology, CPU limits, and protocol flags
- **CPU limits:** analyzed the impact of CPU constraints on IB propagation, finding that diffusion can be affected under stress conditions
- **Vote propagation:** compared freshest-first and oldest-first vote propagation, with freshest-first potentially improving IB delivery reliability
- **Extended voting period:** compared an extended voting period to a limited one in the Haskell simulation, observing minimal differences except for occasional improvements in reliable vote delivery.

## Ongoing investigations

- Investigating qualitative discrepancies between Haskell and Rust simulation results to determine whether they stem from differences in simulator resolution or simulation infidelities.

## Additional resources

- [Monthly review meeting](https://www.youtube.com/watch?v=7K6qXiVsMXg) – March 2025.
