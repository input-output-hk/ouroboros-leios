---
title: Weekly Summary – April 28, 2025
authors:
- will
tags: [progress, update, weekly]
---

This week, the Leios team made significant progress in protocol documentation, simulation improvements, and transaction lifecycle analysis. The team completed a draft of the Leios CIP, enhanced simulation visualization capabilities, and conducted detailed analysis of transaction processing times in Full Leios.

## Simulation and analysis

- Completed simulation of 270 Full Leios scenarios at tag [`leios-2025w17`](https://github.com/input-output-hk/ouroboros-leios/releases/tag/leios-2025w17)
- Resolved all outstanding discrepancies between Rust and Haskell simulation results
- Conducted detailed transaction lifecycle analysis:
  - Average IB inclusion time: 2.4 seconds
  - Average EB referencing time: 27.6 seconds
  - Average RB referencing time: 67.2 seconds
  - Identified issues with transaction referencing and duplication in current Full Leios implementation.

## Protocol documentation

- Drafted major sections of the [Leios CIP](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/cip/README.md) using standard CIP template
- Documented evidence-based arguments for Leios necessity and viability
- Pending completion of Full Leios protocol sections due to ongoing discussions.

## Rust implementation

- Publicly hosted visualization as part of the Leios documentation
- Added new "transactions" view showing transaction state graphs over time
- Fixed stability issues in long-running simulations
- Implemented `leios-late-ib-inclusion` extension for referencing older pipeline IBs.

## Plutus benchmarking

- Documented [workflow for benchmarking Plutus](https://github.com/IntersectMBO/plutus/blob/master/plutus-core/cost-model/CostModelGeneration.md)
- Prepared methodology for potential experiments with increased Plutus execution budgets
- Established framework for relating Plutus execution units to CPU time measurements.

## Next steps

- Address transaction referencing and duplication issues in Full Leios
- Complete remaining Full Leios protocol sections in CIP
- Investigate higher transaction rates after resolution of [#305](https://github.com/input-output-hk/ouroboros-leios/issues/305)
- Continue monitoring and optimizing transaction lifecycle performance.
