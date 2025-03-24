---
title: Weekly Summary - 2025-03-17
authors:
- will
tags: [progress, update, weekly]
---

This week, the team made significant progress in the Leios protocol development, focusing on improving simulation capabilities and understanding the behavior of the protocol in different network conditions. A comparison of Haskell and Rust simulations across **18 scenarios** revealed that Leios protocol scales well to mainnet-size networks. However, the protocol tends to experience congestion once the input-block rate reaches 30 IB/s.

## Simulation comparison

- Compared **18 scenarios** between Haskell and Rust simulations at tag [`leios-2025w12`](https://github.com/input-output-hk/ouroboros-leios/releases/tag/leios-2025w12)
- Recent fixes and adjustments enabled meaningful comparison between simulations
- Identified differences when comparing the Haskell and Rust results, which are under active investigation.

### Analysis of simulations

- Completed the first simulation of Short Leios for varied IB production rate, IB size, and network topology
- In the simulations, the Leios protocol scales well to mainnet-size networks
- Identified congestion in the protocol once the input-block rate reaches 30 IB/s
- Suggested that allowing IBs larger than current Praos RBs may have advantages in TCP efficiency, network usage, and adapting to fluctuating transaction loads

### HasKell simulation

- Implemented expiration of blocks
  - Blocks are cleared from relay buffer as soon as they should stop diffusing, then cleared from other state as specified
- Implemented first stab at Full Leios implementation
  - Only lightly tested so far
  - Added `praos-chain-quality` configuration parameter for the `\eta` parameter from the spec

### Rust simulation

- Implemented first pass at Full Leios, with guesses for some parameters

### Formal methods

- Short Leios trace verification: For Short Leios, we are modelling the local state evolution of a node
- Developed the initial trace verifier for Short Leios simulation traces in `leios-trace-verifier`
