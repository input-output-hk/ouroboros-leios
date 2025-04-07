---
title: Weekly Summary - 2025-03-31
authors:
- will
tags: [progress, update, weekly]
---

This week, the Leios team continued their efforts in refining the protocol and its simulation capabilities. They made significant progress in addressing various aspects of the Haskell simulator.

## Simulation progress

- **Haskell simulation**
  - Added support for dishonest Nodes that diffuse an unbounded amount of old IBs, enabling further analysis of freshest-first and oldest-first vote delivery scenarios
  - Identified and fixed a bug in config generation for simulation runs, which was causing inconsistencies in vote delivery between default and uniform/extended voting schemes
  - Added an `adversarial` field to the network topology schema, allowing for the simulation of unbounded IB diffusion by dishonest nodes

## Analysis of simulations

No specific scenario analysis was reported for this week. However, the team continues to investigate the impact of dishonest nodes on vote delivery and IB diffusion.

## Ongoing investigations

- Investigating the effects of unbounded IB diffusion on IB delivery reliability and the performance of the protocol under such conditions.

## Additional resources

- [GitHub discussion](https://github.com/input-output-hk/ouroboros-leios/discussions/243) – EB ledger states and "history rewriting" effects.

Note: A daily review was not available, however, notes were found for the dates 2025-04-04.
