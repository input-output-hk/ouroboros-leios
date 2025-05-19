---
title: Weekly Summary - 2025-05-12
authors:
- will
tags: [progress, update, weekly]
---

Here is a weekly summary for the period from 2025-05-12 to 2025-05-19.

### Weekly Summary - 2025-05-12 to 2025-05-19

This week, the team made significant progress on various fronts, including protocol documentation, security improvements, and simulation analysis.

### Protocol Documentation and Analysis

The team continued working on the Leios protocol documentation, producing several key visualizations to demonstrate transaction throughput and block characteristics.

<div align="center">

![Transaction throughput analysis](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/refs/heads/main/analysis/block-praos-leios-contour.svg)

*Figure 1: Transaction throughput as a function of block size and rate*

![Comparative transaction lifecycle](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/refs/heads/main/analysis/tx-to-block-fig.svg)

*Figure 2: Comparative transaction lifecycle between Praos and Leios*

</div>

The team also conducted an extensive profitability analysis for Leios SPOs, considering various deployment scenarios. The analysis included evaluating infrastructure costs across premium and value cloud providers, demonstrating profitability without reserve contributions at 50+ TPS, and documenting the impact of diminishing future rewards due to reserve depletion.

### Simulation Analysis and Performance

The team conducted high-throughput simulations of Leios using the Rust simulator, with transaction rates reaching up to 1,000 TPS. They introduced two key efficiency metrics to quantify system performance: temporal efficiency, which measures the fraction of submitted transactions that make it into the ledger, and spatial efficiency, which represents the ratio of transaction size to total ledger size.

Recent revisions to Full Short Leios have shown promising improvements in both efficiency metrics. The simulations revealed an average transaction lifecycle of approximately 100 seconds from submission to ledger inclusion.

### Security and Infrastructure Improvements

The team addressed several security vulnerabilities in web applications through a series of patches.

### Protocol Enhancements

Recent protocol improvements include:

- Implementation of revisions to Full Short Leios design to enhance both temporal and spatial efficiency
- Optimization of protocol parameters for improved transaction processing
- Development of a new sharding strategy in Rust simulation
- Enhanced logging system for tracking spatial efficiency metrics.

### Notable Updates

- Two manually curated test cases for the Leios trace verifier were created and integrated into a new test suite.
- Deterministic conformance testing was removed and replaced with non-deterministic, trace-based conformance testing.
- The Leios trace verifier was added to the Nix infrastructure and the CI builds.
- Two partially-drafted technical reports related to the Haskell simulations were added to the Nix and CI builds.

For more detailed information about the simulations and analysis, please refer to the [analysis documentation](https://github.com/input-output-hk/ouroboros-leios/tree/main/analysis) and the [profitability analysis notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/profitability-leios.ipynb).
