---
title: Weekly Summary – March 10, 2025
authors:
- will
tags: [progress, update, weekly]
---

This week saw significant progress in simulation capabilities with the successful comparison of Rust and Haskell simulations across **[90 scenarios](https://github.com/input-output-hk/ouroboros-leios/blob/weekly-update-2025-03-10/analysis/sims/2025w11/analysis.ipynb)**. We conducted our **first mainnet-scale [analysis](https://github.com/input-output-hk/ouroboros-leios/blob/weekly-update-2025-03-10/analysis/sims/2025w11xl/analysis.ipynb) of Leios** on a [mainnet-scale network](https://github.com/input-output-hk/ouroboros-leios/blob/leios-2025w11/sim-rs/test_data/realistic.yaml) of 3000 nodes, revealing unexpected performance benefits from network topology. **[Sharding performance analysis](https://github.com/input-output-hk/ouroboros-leios/blob/weekly-update-2025-03-10/analysis/shard-performance.ipynb)** provided important insights into optimization strategies. Both simulation implementations received improvements to enhance realism and comparability, while our formal methods team developed initial trace verification tools for Short Leios.

## Simulation comparison

- Compared [90 scenarios](https://github.com/input-output-hk/ouroboros-leios/blob/weekly-update-2025-03-10/analysis/sims/2025w11/analysis.ipynb) between Rust and Haskell simulations at tag [`leios-2025w11`](https://github.com/input-output-hk/ouroboros-leios/releases/tag/leios-2025w11)
- Recent fixes and adjustments enabled meaningful comparison between simulations
- Identified [issues](https://github.com/input-output-hk/ouroboros-leios/issues?q=is%3Aissue%20state%3Aopen%20label%3Aquestion) requiring further investigation.

### Analysis of mainnet-scale simulation

- Completed first [analysis](https://github.com/input-output-hk/ouroboros-leios/blob/weekly-update-2025-03-10/analysis/sims/2025w11xl/analysis.ipynb) of Leios on a mainnet-scale network simulation using Rust simulator
- Discovered 3000-node mainnet-scale network transports IBs faster than artificial 100-node network
- Identified "shortcut" edges in larger networks as likely reason for improved transport speed.

![In-flight time for Input Blocks (IBs)](https://github.com/input-output-hk/ouroboros-leios/blob/weekly-update-2025-03-10/analysis/sims/2025w11xl/plots/elapsed-IB-rust.png?raw=true)

### Performance analysis of sharding

- Created [computational models](https://github.com/input-output-hk/ouroboros-leios/blob/weekly-update-2025-03-10/analysis/shard-performance.ipynb) showing relationship between fraction of shards without an IB and expected number of extra IBs
- Evaluated performance characteristics of the simplest sharding scheme.

![Performance analysis of simple sharding](https://github.com/input-output-hk/ouroboros-leios/raw/weekly-update-2025-03-10/analysis/shard-performance.svg)

## Haskell simulation

- Fixed bug in Relay protocol preventing full diffusion of votes
- Changed priority of certified EB to be included in RB
- Added support for output log format sharing a common subset with the Rust sim
- Analyzed TCP realism in comparison to idealized diffusion
  - Found higher IB rate and size leads to better diffusion times
  - Identified ledger state access as significant source of latency.

## Rust simulation

- Added more information to logs (total size of IB, parent id of RB)
- Implemented same EB selection strategy as Haskell
- Added validation of IB headers before propagation to neighbors
- Investigating why the simulation doesn't encounter as much congestion as Haskell.

## Formal methods

- Developed initial trace verifier for Short Leios simulation traces in `leios-trace-verifier`.
