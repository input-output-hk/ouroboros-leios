---
title: Weekly Summary - 2025-03-10
authors:
- will
tags: [progress, update, weekly]
---

## High-level summary

This week in Leios development, the team focused on Haskell and Rust simulation analysis, formal methods, and documentation updates. Key accomplishments include in-depth analysis of simulations, advancements in formal methods through a working trace verifier, and the development of technical reports.

## Cross-simulation analysis

- Conducted a deeper analysis of simulations at tag `leios-2025w11`:
  - Resolved issues raised by the simulation comparison for both Haskell and Rust simulations.
  - Fixed bug in Relay protocol preventing full diffusion of votes for Haskell.
  - Implemented similar EB producer discretion in serialization order of IBs for both simulations.
  - Found significant sources of latency in both Haskell and Rust simulations, including access to the ledger state necessary to validate IBs.

## Formal methods

- Developed a trace verifier for both Haskell and Rust simulation traces:
  - Implemented the initial version of the `leios-trace-verifier` for Short Leios simulation traces.

## Documentation and research

- Updated the full draft of the [Leios technical report](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/technical-report-1.md) with new simulation findings.
- Completed a [skeletal draft](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/leios-cip-draft.md) of the Leios CIP.
- Developed a detailed simulation analysis for a 100-node Leios network and a mainnet-scale 3000-node network.
- Added visualizations for resource utilization in network traffic.

## Rust simulation analysis

- Analyzed mainnet-scale simulation results for a 3000-node network:
  - Compared mainnet-scale simulation results with artificial 100-node network analysis.
  - Found that the mainnet-scale network transports IBs faster, likely due to long-range shortcut edges.
- Performed performance analysis of sharding:
  - Elucidated the relation between the fraction of shards without an IB and the expected number of extra IBs for the simplest sharding scheme.

## Haskell simulation analysis

- Addressed various issues raised by the simulation comparison:
  - Fixed bug in Relay protocol preventing full diffusion of votes.
  - Changed priority of certified EB to be included in RB.
  - Avoid failing on unknown distributions in config file.
- Added support for output log format that shares a common subset with the Rust sim:
  - Added configurations for both simulations to share a common subset log format.
- Deeper analysis of TCP realism in the comparison to idealized diffusion:
  - Found another significant source of latency is access to the ledger state necessary to validate IBs.
