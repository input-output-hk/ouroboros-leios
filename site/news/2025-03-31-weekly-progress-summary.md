---
title: Weekly Summary – March 31, 2025
authors:
- will
tags: [progress, update, weekly, workshop, edinburgh, ledger-design, cost-analysis, optimistic-validation, formal-methods, haskell-simulation, adversarial]
---

This week, the Leios team met for an in-person workshop in Edinburgh and continued their efforts in refining the protocol and its simulation capabilities. The team made significant progress in addressing various topics.

# Workshop summaries

On [day one](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-1-recap.md), the team discussed topics such as ledger design and trade-offs, as well as two different ways to link the formal specification to the simulations. They explored various ledger design options, including *labeled UTXOs* and *accounts* approaches, with detailed consideration of fees, collateral, and conflict prevention mechanisms. The team also discussed conformance testing approaches, including *QuickCheck dynamic and trace verification* methods.

On [day two](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-2-recap.md), the team made significant progress towards estimating the cost of running a Leios node, considering different cost items such as network egress, CPU, and storage. They analyzed resource usage across different TPS levels, from 10 TPS to 1K TPS, and discovered that while there’s significant overhead at low throughput, the protocol becomes more efficient at higher TPS levels. The team hasn’t been able to finish all the cost items yet. The last two, IOPS and memory cost, will be added during this month.

On the [last and third day](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-3-recap.md), the team consolidated their options for how optimistic validation of input blocks can be accomplished. They defined three candidates, with one being favored. The main goal was to support the chaining of transactions with Leios, which requires defining a 'point in time' or stage of the protocol at which a subsequent or chained transaction can be built on top of an already submitted transaction. This can be achieved by having the node optimistically compute prospective ledger states using its local knowledge of input blocks referenced in certified endorser blocks or possibly ranking blocks.

- [Day 1](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-1-recap.md)

- [Day 2](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-2-recap.md)

- [Day 3](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-3-recap.md).


## Simulation progress

- **Haskell simulation**
  - Added support for dishonest nodes that diffuse an unbounded amount of old IBs, enabling further analysis of freshest-first and oldest-first vote delivery scenarios
  - Identified and fixed a bug in configuration generation for simulation runs, which was causing inconsistencies in vote delivery between default and uniform/extended voting schemes
  - Added an `adversarial` field to the network topology schema, allowing for the simulation of unbounded IB diffusion by dishonest nodes.

## Ongoing investigations

- Investigating the effects of unbounded IB diffusion on IB delivery reliability and protocol performance under such conditions
- Working on quantifying settlement times and their impact on protocol performance
- Exploring integration possibilities with Ouroboros Peras, mainly focusing on potentially reusing their voting mechanism to reduce resource consumption.

## Additional resources

- [GitHub discussions](https://github.com/input-output-hk/ouroboros-leios/discussions/243) – EB ledger states and 'history rewriting' effects
- [The First Full Leios simulation analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w13/analysis.ipynb) – detailed analysis of the latest simulation results.
