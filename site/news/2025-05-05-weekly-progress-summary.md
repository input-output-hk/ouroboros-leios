---
title: Weekly Summary – May 5, 2025
authors:
- will
tags: [progress, update, weekly, high-throughput, simulation-analysis, efficiency-metrics, security, profitability-analysis, rust-simulation, visualization]
---

This week, the team focused on simulation analysis, security improvements, and protocol documentation, making significant progress across multiple areas.

### Simulation analysis and performance

The team executed the first high-throughput simulations of Leios using the Rust simulator, with transaction rates reaching up to 1,000 TPS. They introduced two key efficiency metrics to quantify system performance:

- *Temporal efficiency*, which measures the fraction of submitted transactions that make it into the ledger, with nearly 100% indicating optimal transaction inclusion
- *Spatial efficiency*, which represents the ratio of transaction size to total ledger size (including IBs, EBs, and RBs), with higher values indicating better storage optimization.

Recent revisions to Full Short Leios have shown promising improvements in both efficiency metrics. The simulations revealed an average transaction lifecycle of approximately 100 seconds from submission to ledger inclusion.

The analysis produced several key visualizations that demonstrate the system's performance:

<div align="center">

![Temporal efficiency bar chart](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/refs/heads/main/analysis/sims/2025w19/plots/temporal-efficiency-bar.svg)

*Figure 1: Temporal efficiency comparison across different transaction rates*

![Temporal efficiency time series](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/1a7ccb588bf87284858c05a0670b938b5d35c417/analysis/sims/2025w19/plots/temporal-efficiency-timeseries.svg)

*Figure 2: Temporal efficiency trends over time*

![Spatial efficiency analysis](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/refs/heads/main/analysis/sims/2025w19/plots/spatial-efficiency.svg)

*Figure 3: Spatial efficiency analysis showing ledger optimization*

![Transaction lifecycle visualization](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/refs/heads/main/analysis/sims/2025w19/plots/reach-rb-tx.svg)

*Figure 4: Transaction lifecycle from submission to ledger inclusion*

</div>

### Protocol documentation and analysis

The team conducted an extensive analysis of transaction throughput and block characteristics, producing several key visualizations:

<div align="center">

![Transaction throughput analysis](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/refs/heads/main/analysis/block-praos-leios-contour.svg)

*Figure 5: Transaction throughput as a function of block size and rate*

![Comparative transaction lifecycle](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/refs/heads/main/analysis/tx-to-block-fig.svg)

*Figure 6: Comparative transaction lifecycle between Praos and Leios*

</div>

The team also completed a comprehensive profitability analysis for Leios SPOs, considering various deployment scenarios:
- Evaluated infrastructure costs across premium and value cloud providers
- Demonstrated profitability without reserve contributions at 50+ TPS
- Documented the impact of diminishing future rewards due to reserve depletion
- Analyzed comparative economics between Praos and Leios SPOs.

<div align="center">

![Profitability forecast visualization](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/refs/heads/main/analysis/leios-forecast-sqrt-fill.svg)

*Figure 7: Profitability forecast for Leios SPOs without reserve contributions*

</div>

### Security and infrastructure improvements

The team addressed several security vulnerabilities in web applications through a series of patches:
- Fixed minor and moderate security issues in [#321](https://github.com/input-output-hk/ouroboros-leios/pull/321), [#322](https://github.com/input-output-hk/ouroboros-leios/pull/322), [#323](https://github.com/input-output-hk/ouroboros-leios/pull/323), and [#325](https://github.com/input-output-hk/ouroboros-leios/pull/325) pull requests.

### Protocol enhancements

Recent protocol improvements include:
- Implementation of revisions to Full Short Leios design to enhance both temporal and spatial efficiency
- Optimization of protocol parameters for improved transaction processing
- Development of a new sharding strategy in Rust simulation
- Enhanced logging system for tracking spatial efficiency metrics.

For more detailed information about the simulations and analysis, please refer to the [analysis documentation](https://github.com/input-output-hk/ouroboros-leios/tree/main/analysis) and the [profitability analysis notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/profitability-leios.ipynb).
