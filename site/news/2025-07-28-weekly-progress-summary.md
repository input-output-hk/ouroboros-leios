---
title: Weekly Summary – July 28, 2025
authors:
- will
tags: [progress, update, weekly, linear-leios, simulation-comparison, network-topology, stage-length, haskell-simulation, rust-simulation]
---

This week, the Leios team focused on comparative analysis between simulation implementations and conducted experiments examining the impact of protocol parameters and network topology on Linear Leios performance. The team made progress in cross-validation between Haskell and Rust simulations while investigating protocol behavior under different network conditions.

## Cross-simulation analysis

### Haskell vs Rust Linear Leios comparison

The team completed a comprehensive comparison between the early draft Haskell simulator and the more mature Rust simulator for Linear Leios. Key findings from the analysis documented in [analysis/sims/2025w31b/analysis.ipynb](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w31b/analysis.ipynb) revealed several discrepancies requiring investigation:

- CPU usage patterns differed between implementations
- Network usage showed variations across simulators  
- Vote diffusion behavior exhibited inconsistencies
- [Active investigation](https://github.com/input-output-hk/ouroboros-leios/pull/466) underway to resolve implementation differences.

## Protocol parameter experiments

### Stage length analysis for "No IBs" Leios

The team conducted experiments varying the stage-length protocol parameter from 5 to 12 slots per stage in "No IBs" Leios. Results documented in [analysis/sims/2025w31/analysis.ipynb](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w31/analysis.ipynb) showed:

- Settlement time remains relatively stable across the tested parameter range
- Stage length has minimal impact on transaction processing times within 5-12 slot range
- Larger stage lengths result in less frequent voting periods
- Protocol performance appears robust to moderate stage length variations.

## Network topology validation

### Mini-mainnet vs pseudo-mainnet comparison

The team completed a comparative analysis of Linear Leios performance across different network topologies using the Rust simulator. Key findings from [analysis/sims/2025w30b/analysis.ipynb](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w30b/analysis.ipynb) include:

- The 750-node mini-mainnet network proved slightly more stressful to the protocol than the 10,000-node pseudo-mainnet
- No substantial differences in simulation results between the two network configurations
- Both networks produce equivalent findings and conclusions for protocol analysis
- Validation confirms the mini-mainnet topology as a suitable proxy for larger-scale analysis.

## Rust simulation enhancements

### Linear Leios attack modeling

- Added equivocation voting delay functionality to Linear Leios implementation
- Implemented attack scenario modeling where endorser block (EB) diffusion is deliberately delayed until the last moment
- Enhanced simulation capabilities for security analysis and adversarial behavior testing.

## Next steps

- Continue investigation of discrepancies between Haskell and Rust Linear Leios implementations
- Expand parameter sensitivity analysis for additional protocol variants
- Refine attack modeling capabilities for comprehensive security assessment
- Apply lessons from network topology comparison to future experimental design.
