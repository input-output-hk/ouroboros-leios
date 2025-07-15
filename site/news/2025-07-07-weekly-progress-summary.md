---
title: Weekly Summary – July 7, 2025
authors:
- will
tags: [progress, update, weekly, high-throughput, protocol-variants, stracciatella, linear-leios, simulation-analysis, cddl]
---

This week, the Leios team achieved significant milestones in protocol development and analysis, successfully demonstrating high-throughput capabilities and exploring new protocol variants. The team completed comprehensive experiments with the Stracciatella variant, conducted analytical analysis of Linear Leios throughput efficiency, and implemented new simulation capabilities.

## High-throughput demonstration

- Successfully completed experiments demonstrating 1,000+ TPS capability with the Stracciatella variant of Leios.
- Achieved spatial efficiency better than 95% with transaction lifecycle times under two minutes.
- Validated protocol performance under extreme throughput conditions significantly beyond current Cardano capacity.
- Documented detailed findings in the [Stracciatella analysis notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w28/analysis-stracciatella.ipynb).

## Protocol variants analysis

### Stracciatella variant

- Completed comprehensive analysis of the Stracciatella variant (no IBs, transaction references in EBs, two-stage pipeline).
- Key findings:
  - 5 slot/stage performs less well but scales better than 8 slot/stage.
  - Only minimal fraction of transactions fail to reach ledger, likely due to EB expiration.
  - Network usage is slightly heavy while CPU usage appears suspiciously light.
  - Congestion appears at 1,000+ TPS throughput levels.

### Linear Leios throughput efficiency

- Conducted analytical analysis of Linear Leios variant's probability of including certified EBs on-chain.
- Results show Linear Leios could achieve approximately 500 times the throughput of Praos at over 50% network resource efficiency.
- 500 times Praos throughput would exceed 1,000 historically typical transactions per second.
- Generated comprehensive throughput and efficiency visualizations available in the [analysis repository](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/).

![Throughput of Linear Leios](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/main/analysis/linear-leios-throughput.svg)

![Throughput efficiency of Linear Leios](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/main/analysis/linear-leios-efficiency.svg)

## CDDL specifications

- Added CDDL specifications for Linear and Stracciatella protocol variants.

## Simulation improvements

### Rust simulation

- Implemented first pass at Linear Leios variant in Rust simulation.
- Enhanced simulation capabilities for protocol variant testing and analysis.
- Continued optimization of simulation performance for high-throughput scenarios.

### Small transaction experiments

- Completed analysis of small-transaction, high-throughput experiments with 300-byte non-Plutus transactions.
- Key findings:
  - 1,000 tx/s with 300 B/tx is feasible in Leios variants.
  - Clear time vs space tradeoff between variants.
  - `full-with-ib-references` uses space more efficiently than `full-without-ibs`.
  - `full-without-ibs` has shorter transaction lifecycle than `full-with-ib-references`.
  - 2 CPU cores are sufficient for high-throughput operation.
  - Network usage remains modest under high load.
- Supporting materials available in [analysis documentation](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w28/ReadMe.pdf) and [analysis notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w28/analysis.ipynb).

## Next steps

- Continue investigation of protocol variants for CIP convergence.
- Expand simulation capabilities for additional protocol variants.
- Refine performance optimization strategies for high-throughput scenarios.
- Complete documentation of protocol variant comparisons and recommendations.

