---
title: Weekly Progress Summary - January 7, 2025
authors:
- will
tags: [progress, update, weekly]
---

## Weekly Overview

Last week, the Leios team focused on advancing Rust simulations, particularly in
simulating network and processing behaviors similar to those on the Cardano
mainnet. This involved enhancing central processing unit (CPU) event logging and
experimenting with how block and vote diffusion change with different protocol
parameters. They also updated the cost dashboard with revised parameters and
computations, aligning these with empirical data and preparing for further
calibration.

## Rust Simulation

- Simulated infinite CPUs and output CPU events in logs.
- Enhancements include:
  - Added basic simulation of CPU usage/latency.
  - Introduced "lottery won" events to identify the start of CPU processing.
  - Configured each node with four simulated cores for CPU-bound tasks.
  - Transaction validation and ranking block/input block/endorser block
    generation/validation each take one CPU task.
  - All virtual CPU costs were copied from the cost estimator.

## DeltaQ

- Added MIN/MAX combinators for best- and worst-case simulation results.
- The Rust simulation best case does not match the analytically best behavior.
- The Haskell simulation best case is too fast; the ΔQ expression must assume
  more than 200 peers per node.
- Concluded that this workstream has failed due to discrepancies in simulation
  results.

## Summary of December 17 Q&A Discussion

- Discussed the throughput dashboard and its potential as a formal website.
- Explored the impact of Leios on ledger changes, data structures, and the
  ecosystem.
- Considered using Mithril for proofs of equivocation.
- Discussed the elasticity and adaptability of nodes.
- Explored interactions between emerging Hydra protocols and layer 1.

## Cost Dashboard Updates

- Updated the dashboard with improved parameters and computations:
  - Lengthened phases and reduced the endorser block rate based on technical
    report analysis.
  - Revised CPU costs for votes and certificates according to the technical
    report.
  - Updated input/output operations per second (IOPS) values using empirical
    Cardano node production data.
  - Aligned and cross-validated Agda code with the web interface.
  - Future updates are pending calibration data from Haskell/Rust simulations.

## Summarized Update for the Essential Cardano Report

Ouroboros Leios is another research and development project that the IO teams
are working on. Leios aims to increase Cardano’s throughput by optimizing
available network resources and enabling faster transaction processing and
confirmation.

Last week, the Leios team worked on enhancing Rust simulations and refining
central processing unit (CPU) event logging. Key updates included simulating
infinite CPUs, adding basic CPU usage/latency simulations, and configuring nodes
with four simulated cores. The team also worked on improving the DeltaQ work
stream, introducing MIN/MAX combinators for best- and worst-case simulation
results. However, discrepancies between Rust and Haskell simulation results led
to the conclusion that the DeltaQ workstream did not meet the expected outcomes.
