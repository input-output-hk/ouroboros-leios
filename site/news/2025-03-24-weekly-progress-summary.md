---
title: Weekly Summary - 2025-03-24
authors:
- will
tags: [progress, update, weekly]
---

**Weekly Summary (2025-03-24 to 2025-03-31)**

This week, the Leios team continued working on various aspects of the protocol and simulation capabilities. The team made progress on implementing and testing the Haskell and Rust simulators, focusing on protocol behavior under different network conditions.

## Simulation Progress

- **Haskell simulation:**
  - Moved configuration and topology parsers to the `leios-trace-hs` package for reuse by formal methods.
  - Investigated differences in IBs referenced with Rust simulation: inconsistencies in their distribution are due to the same sequence of random samples being used across different runs.
  - Simplified sortition code by relying on the external statistics package.
  - Tested Full Leios, resolving tension between `r_EB`/`eb-max-age-slots` and `praos-chain-quality`/`η`.
  - Fixed `cabal run ols -- generate-topology close-and-random`, listing `producers` properly and decreasing variance in upstream peers.

- **Rust simulation:**
  - Investigated oddities in simulation results: IB production broke down earlier due to low connectivity, and CPU usage is lower than Haskell sim.
  - Refined Full Leios implementation.
  - Added Full Leios support to the visualizer.
  - Moved the visualizer off Next.js and onto vite.

## Analysis of Simulations

- **Tag `leios-2025w13`:** Simulated 198 scenarios of Short Leios for varied IB production rate, IB size, and network topology, CPU limits, and protocol flags.
- **CPU limits:** Studied how limiting available CPU affects IB propagation and discovered that CPU can impact diffusion under stressful scenarios.
- **Vote propagation:** Compared freshest-first and oldest-first vote propagation, with freshest-first potentially improving IB delivery reliability.
- **Extended voting period:** Compared an extended voting period versus a limited one in the Haskell simulation, revealing little difference except for rare improvements in reliable vote delivery.

## Ongoing Investigations

- Investigating qualitative discrepancies between Haskell and Rust simulators' results to determine whether they are due to simulator resolution or simulation infidelities.

## Tools

- **Egress Traffic Calculator:**
