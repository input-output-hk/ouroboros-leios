---
title: Weekly progress summary - January 27, 2025
authors:
- will
tags: [progress, update, weekly]
---

## Haskell simulation updates

- `short-leios` simulation now outputs diffusion latency data
- Added support for different IB diffusion strategies:
  - freshest-first: higher slot numbers requested first
  - peer-order: requested in order of peer announcement
- Added support for Vote (Send) and Vote (Recv) stages

## Rust simulation progress

- Added an "organic" topology generator that better matches mainnet topology
- Generator creates clusters of colocated stake pools and relays
- Uses stake to determine relay connectivity
- Topology insights gathered from stake pool owners:
  - Most pools have multiple relays (2312 relays across 1278 pools counted)
  - Pool operators often run multiple colocated pools sharing relays
  - Relays typically maintain ~25 active outgoing connections
  - Incoming connections scale with stake weight (10-400+ connections)

## DeltaQ update

- Wrote a comprehensive report covering work since September 2024
- Report available at [Report 2025-01.md](./delta_q/docs/Report%202025-01.md)

## Formal Methods

- Finalizing executable specifications for Simplified and Short Leios
- Short Leios spec extracted to Haskell for conformance testing
