---
title: Weekly Summary – March 17, 2025
authors:
- will
tags: [progress, update, weekly]
---

This week, the Leios team made significant progress in protocol development, focusing on improving simulation capabilities and analyzing protocol behavior under various network conditions. A comparison of Haskell and Rust simulations across [**18 scenarios**](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w12/analysis.ipynb) demonstrated that the Leios protocol scales effectively to mainnet-sized networks. However, congestion occurs when the input block rate reaches 30 IB/s.

## Simulation comparison

- Compared [**18 scenarios**](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w12/analysis.ipynb) between Haskell and Rust simulations at tag [`leios-2025w12`](https://github.com/input-output-hk/ouroboros-leios/releases/tag/leios-2025w12)
- Recent fixes and adjustments enabled meaningful comparison between simulations
- Identified differences when comparing the Haskell and Rust results, which are under active investigation.

### Analysis of simulations

- Completed the first simulation of Short Leios, evaluating IB production rate, IB size, and network topology
- Demonstrated that the Leios protocol scales effectively to mainnet-sized networks
- Identified congestion occurring when the input block rate exceeds 30 IB/s
- Suggested that allowing IBs larger than current Praos RBs may have advantages in TCP efficiency, network usage, and adapting to fluctuating transaction loads.

| Peak CPU                                                                                                               | Mean CPU                                                                                                               |
|------------------------------------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------------------------------------|
| ![analysis/sims/2025w12xl/plots/cpu-peak-histogram-rust.png](https://github.com/input-output-hk/ouroboros-leios/raw/main/analysis/sims/2025w12xl/plots/cpu-peak-histogram-rust.png) | ![analysis/sims/2025w12xl/plots/cpu-mean-histogram-rust.png](https://github.com/input-output-hk/ouroboros-leios/raw/main/analysis/sims/2025w12xl/plots/cpu-mean-histogram-rust.png) |

### Haskell simulation

- Implemented expiration of blocks:
  - Blocks are removed from the relay buffer once diffusion stops and cleared from other states as specified
- Developed an initial Full Leios implementation:
  - Currently in early testing
  - Added the `praos-chain-quality` configuration parameter for the `\eta` parameter from the specification.

### Rust simulation

- Developed an initial Full Leios implementation using estimated values for some parameters.

### Formal methods

- Short Leios trace verification: modeling local state evolution of a node 
- Developed an initial trace verifier for Short Leios simulation traces in `leios-trace-verifier`.
