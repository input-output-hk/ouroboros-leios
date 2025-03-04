---
title: Weekly Progress Summary - 2025-02-24
authors:
- will
tags: [progress, update, weekly]
---

## Weekly Summary for 2025-02-24 to 2025-03-03

## High-level summary

This week in simulation analysis, the team focused on Haskell simulation advancements, updated the Rust simulation, and cleared up previous discrepancies in congestion metrics. Key accomplishments included resolving issues related to IB sortition, integrating a block expiration/diffusion-halt proposal, and updating bandwidth calculations in the Rust simulation.

## Haskell Simulation Analysis

- Completed IB sortition fix for cases where `IB/slot < 1`.
- Integrated block expiration/diffusion-halt proposal, allowing for comparison between idealized and simulated node configurations.
  - Added `treat-blocks-as-full` config parameter to promote uniform block behavior network and CPU usage.
  - Noted improvements in preliminary results: `treat-blocks-as-full` promises a better simulation environment, though Relay mini-protocol complications still exist.
    - Relay can require either 3 or 4 latency messages to transfer a new block.

## Rust Simulation Update

- Updated bandwidth calculations to employ a strict First-In-First-Out (FIFO) configuration.
  - Bandwidth is no longer divided between parallelized requests for individual mini-protocols. However, bandwidth splitting between all mini-programs is still inaccurate due to its current configuration.

## Lessons learned and Future work

- Continue testing IB sortition and block expiration/diffusion-halt proposal to promote further improvements in simulation outcomes.
- Investigate potential modifications to bandwidth calculations in the Rust simulator to improve compatibility with network configurations.
- Address and rectify issues concerning latency required for data to propagate through Relay mini-protocol.
