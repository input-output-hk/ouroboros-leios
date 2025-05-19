---
title: Weekly Summary - 2025-05-12
authors:
- will
tags: [progress, update, weekly]
---

This week, the team made significant progress on simulation improvements, trace verification, and comprehensive analysis of Leios transaction processing capacity.

### Trace verification

- Improved the trace verifier with better error handling and reporting
- Added support for starting verification from non-initial states
- Created manually curated test cases for the Leios trace verifier
  - [Valid traces](https://github.com/input-output-hk/ouroboros-leios/blob/main/leios-trace-verifier/examples/valid/)
  - [Invalid traces](https://github.com/input-output-hk/ouroboros-leios/blob/main/leios-trace-verifier/examples/invalid/)
- Integrated the trace verifier into Nix infrastructure and CI builds
- Removed deterministic conformance testing in favor of trace-based approach.

### Simulation improvements

#### Haskell simulation
- Conducted an informal review assessing code quality, design, and implementation
- Analyzed the simulation organization and identified areas for future improvement
- Found that most prospective changes to the Leios protocol would only involve a small fraction of the codebase
- Determined that addition of memory pool and transactions would take approximately 100-200 hours of labor.

The review of the Haskell simulator was documented in detail in [PR#353](https://github.com/input-output-hk/ouroboros-leios/pull/353), covering statistics, organization, code quality, design, implementation, and documentation aspects of the simulator.

#### Rust simulation
- Added `tx-start-time` and `tx-stop-time` parameters to avoid effects of slow starts or sudden terminations on transaction analysis
- Created a new Leios variant `full-without-ibs` where endorser blocks directly reference transactions.

### Documentation and analysis

- Relocated the original Leios report to avoid confusion, while preserving valuable background information
- Added partially-drafted technical reports on Haskell simulations to Nix and CI builds:
  - [Ouroboros Leios Network Specification](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/docs/network-spec/ReadMe.md)
  - [Ouroboros Leios simulation: building confidence in the performance results](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/docs/ReadMe.md)

The team conducted higher excess-capacity simulations to evaluate transaction inclusion hypotheses. The transaction lifecycle simulations raised the question of whether duplication of transactions in IBs was starving other transactions from ever being included in an IB. To test this, simulations were run with IBs being produced at three times the normal rate, providing ample space for transaction duplication.

Detailed analysis showed that transaction loss persisted despite increased capacity, indicating that other factors are preventing transactions from reaching the ledger. The results are documented in:
- [Analysis overview](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w20/)
- [Results at 1x IB capacity](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w20/analysis1x.ipynb)
- [Results at 3x IB capacity](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w20/analysis3x.ipynb)

