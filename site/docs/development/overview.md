---
sidebar_position: 1
---

# Overview

The Ouroboros Leios project is currently in research and development.

The Input | Output Research (IOR) team is in the process of assessing ways to increase Cardano’s transaction throughput while maintaining security and decentralization. This work includes modeling the growth of transactions, the economics of stake pools, and the dynamics of ledger size over multiple epochs. 

The current research areas include:

- **Formal methods.** Ensures the Leios protocol is rigorously defined and validated. This includes extracting executable specifications, running conformance tests, and aligning simulations with formal proofs. 
- **Haskell simulation.** Reuses the typed framework to implement mini-protocols similar to those on Cardano mainnet. The simulation can generate visualizations if configured, but typically runs on a smaller network topology than Rust.
- **Rust simulation.** Focuses on simulating the complete network, providing a more realistic test environment for the protocol compared to the Haskell simulation.
- **Cross-simulation analysis.** Compares results between Haskell and Rust simulations to validate findings and ensure consistency. Key focuses include protocol breakdown thresholds under high transaction loads, qualitative similarities between different models, and efforts to standardize input and output formats.
- **DeltaQ analysis.** A method for evaluating network performance by modeling inter-node latencies and classifying near/far connections. It helps predict congestion points and analyze protocol efficiency.
- **Infrastructure improvements.** Enhancing tools and workflows, such as adding Docker support for simulations, developing new topology generators, and refining cost models for deployment scenarios.

:::info
Stay informed on the latest developments by visiting the [Weekly updates](https://leios.cardano-scaling.org/news) page. Development updates cover additional simulation scenarios, parameter tuning, and ongoing research focuses.
:::

## Roadmap snapshot

- **Short term.** Fine-tune the model to capture real-world conditions, such as annual hardware cost declines.
- **Midterm.** Integrate outputs from the model into other Cardano tools and simulations to create a more holistic view of network health.
- **Long term.** Use model insights to inform consensus protocol upgrades, including advanced compression and fee strategies.
