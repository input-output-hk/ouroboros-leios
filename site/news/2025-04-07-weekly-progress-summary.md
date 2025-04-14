---
title: Weekly Summary - 2025-04-07
authors:
- will
tags: [progress, update, weekly]
---

This week, the team continued their efforts in refining the protocol and its simulation capabilities. The team made significant progress in addressing various topics.

# Workshop summaries

Unfortunately, there are no workshop summaries for this week. If another week is provided, I can assist further.

## Simulation progress

- **Haskell simulation**
  - Started specification of a new relay protocol for IB header diffusion without body, documented in `simulation/docs/network-spec`.
  - Removed redundancies and harmonized naming in `--shared-log-format`, with a new base schema both simulations share in `data/simulation/trace.shared.d.ts`.
  - Added support for extra events required by conformance testing, including `SlotEvent` and `NoBlockEvent` in the schema.

## Ongoing investigations

- Investigating the effects of dishonest nodes that diffuse unbounded amounts of old IBs on IB delivery reliability and protocol performance under such conditions.
- Working on quantifying settlement times and their impact on protocol performance.
- Exploring integration possibilities with Ouroboros Peras, mainly focusing on potentially reusing their voting mechanism to reduce resource consumption.

## Additional resources

- [GitHub discussions](https://github.com/input-output-hk/ouroboros-leios/discussions/243) – EB ledger states and 'history rewriting' effects.
