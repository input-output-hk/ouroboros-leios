---
title: Weekly progress summary – January 27, 2025
authors:
- will
tags: [progress, update, weekly]
---
## High-level summary 

The Leios team continued refining Haskell and Rust simulations, standardizing inputs, outputs, and event logging for better comparability. The team defined standard formats [for configuration parameters](https://github.com/input-output-hk/ouroboros-leios/blob/main/data/simulation/config.schema.json) and [network topology](https://github.com/input-output-hk/ouroboros-leios/blob/main/data/simulation/topology.d.ts) for running the Leios protocol. They also worked on logging identical simulation events to compare and feed them into the DeltaQ model and, consequently, the executable specification, ensuring alignment with formal methods.

## Haskell simulation updates

- The `short-leios` simulation now outputs diffusion latency data
- Added support for different input block (IB) diffusion strategies:
  - freshest-first: higher slot numbers requested first
  - peer-order: requested in order of peer announcement
- Added support for `Vote (Send)` and `Vote (Recv)` stages.

## Rust simulation progress

- Added an 'organic' topology generator that better matches mainnet topology
- The generator creates clusters of colocated stake pools and relays
- The simulation uses stake to determine relay connectivity
- Topology insights gathered from stake pool owners:
  - Most pools have multiple relays (2,312 relays across 1,278 pools)
  - Pool operators often run multiple colocated pools sharing relays
  - Relays typically maintain ~25 active outgoing connections
  - Incoming connections scale with stake weight (10-400+ connections).

## DeltaQ update

- Wrote a comprehensive [2025-01 report](https://github.com/input-output-hk/ouroboros-leios/blob/main/delta_q/docs/Report%202025-01.md) covering work since September 2024.

## Formal methods

- Finalizing executable specifications for *simplified* and *short* Leios
- Extracted *short* Leios specification to Haskell for conformance testing.
