---
sidebar_position: 1
---

# Overview

Ouroboros Leios project is a research and development project, which was kicked off in 2024 by the Input | Output Research (IOR) team conducting feasibility studies. This work included modeling the growth of transactions, the economics of stake pools, and the dynamics of ledger size over multiple epochs. 

The original research areas included:

- **Formal methods.** Ensures the Leios protocol is rigorously defined and validated. This includes extracting executable specifications, running conformance tests, and aligning simulations with formal proofs. 
- **Haskell simulation.** Reuses the typed framework to implement mini-protocols similar to those on Cardano mainnet. The simulation can generate visualizations if configured, but typically runs on a smaller network topology than Rust.
- **Rust simulation.** Focuses on simulating the complete network, providing a more realistic test environment for the protocol compared to the Haskell simulation.
- **Cross-simulation analysis.** Compares results between Haskell and Rust simulations to validate findings and ensure consistency. Key focuses include protocol breakdown thresholds under high transaction loads, qualitative similarities between different models, and efforts to standardize input and output formats.
- **DeltaQ analysis.** A method for evaluating network performance by modeling inter-node latencies and classifying near/far connections. It helps predict congestion points and analyze protocol efficiency.
- **Infrastructure improvements.** Enhancing tools and workflows, such as adding Docker support for simulations, developing new topology generators, and refining cost models for deployment scenarios.

The following pages contain various artifacts and outcomes, while the main deliverable and synchronization point with the engineering team was the [Leios CIP](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md). See alo the [engineering roadmap](../roadmap) for current objectives and notable features in development.
