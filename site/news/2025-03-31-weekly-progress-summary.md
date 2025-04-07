---
title: Weekly Summary – March 31st, 2025
authors:
- will
tags: [progress, update, weekly]
---

This week, we met for an in-person workshop in Edinburgh and continued our efforts in refining the protocol and its simulation capabilities. We've made significant progress in addressing various topics.

# Workshop Summaries

On [day one](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-1-recap.md), we discussed topics such as ledger design and trade-offs as well as two different ways how we can link the formal specification to the simulations. We explored various ledger design options including Labeled UTxOs and Accounts approaches, with detailed consideration of fees, collateral, and conflict prevention mechanisms. We also discussed conformance testing approaches, including QuickCheck Dynamic and Trace Verification methods.

[Day two](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-2-recap.md) we made great progress towards estimating the cost of running a Leios node, considering different cost items like network egress, CPU and storage. We analyzed resource usage across different TPS levels, from 10 TPS to 1K TPS, and discovered that while there's significant overhead at low throughput, the protocol becomes more efficient at higher TPS levels. We weren't able to finish all cost items just yet. The last two, IOPS and memory cost, will be added during this month.

On the [last and third day](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-3-recap.md), we consolidated our options how optimistic validation of IBs can be accomplished. We have defined three candidates of which we are favoring one specifically. The main goal was to support chaining of transactions with Leios, which requires to define a "point in time"/ stage of the protocol at which a subsequent/ chained transaction can be built on top of an already submitted transaction. This can be achieved by having the node optimistically compute prospective ledger states using its local knowledge of IBs referenced in certified EBs or possibly RBs.

- [Day 1](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-1-recap.md)

- [Day 2](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-2-recap.md)

- [Day 3](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-3-recap.md)


## Simulation progress

- **Haskell simulation**
  - We added support for dishonest Nodes that diffuse an unbounded amount of old IBs, enabling further analysis of freshest-first and oldest-first vote delivery scenarios
  - We identified and fixed a bug in config generation for simulation runs, which was causing inconsistencies in vote delivery between default and uniform/extended voting schemes
  - We added an `adversarial` field to the network topology schema, allowing for the simulation of unbounded IB diffusion by dishonest nodes

## Analysis of simulations

No specific scenario analysis was reported for this week. However, we continue to investigate the impact of dishonest nodes on vote delivery and IB diffusion.

## Ongoing investigations

- We are investigating the effects of unbounded IB diffusion on IB delivery reliability and the performance of the protocol under such conditions.
- We are working on quantifying settlement times and their impact on protocol performance.
- We are exploring integration possibilities with Peras, particularly focusing on potential reuse of their voting mechanism to reduce resource consumption.

## Additional resources

- [GitHub discussion](https://github.com/input-output-hk/ouroboros-leios/discussions/243) – EB ledger states and "history rewriting" effects.
- [First Full Leios Simulation Analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w13/analysis.ipynb) – Detailed analysis of our latest simulation results.
