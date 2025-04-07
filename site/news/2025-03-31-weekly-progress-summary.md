---
title: Weekly Summary - March 31st, 2025
authors:
- will
tags: [progress, update, weekly]
---

This week, the Leios team met for an in-person workshop in Edinburgh and continued their efforts in refining the protocol and its simulation capabilities. We've made significant progress in addressing various topics.

# Workshop Summaries

On [day one](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-1-recap.md), we have discussed topics such as ledger design and trade-offs as well as two different ways how we can link the formal specification to the simulations.
[Day two](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-2-recap.md) the team has made great progress towards estimating the cost of running a Leios node, considering different cost items like network egress, CPU and storage. We weren't able to finish all cost items just yet. The last two, IOPS and memory cost, will be added during this month.
On the [last and third day](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-3-recap.md), the team has consolidated our options how optimistic validation of IBs can be accomplished. We have defined three candidates of which we are favoring one specifically. The main goal was to support chaining of transactions with Leios, which requires to define a "point in time"/ stage of the protocol at which a subsequent/ chained transaction can be built on top of an already submitted transaction. This can be achieved by having the node optimistically compute prospective ledger states using its local knowledge of IBs referenced in certified EBs or possibly RBs.

- [Day 1](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-1-recap.md)

- [Day 2](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-2-recap.md)

- [Day 3](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/workshop/day-3-recap.md)


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
