---
title: Weekly Summary – February 24, 2025
authors:
- will
tags: [progress, update, weekly]
---

This week in Leios development, the team focused on simulation analysis and formal methods. Key accomplishments include detailed analyses of both Haskell and Rust simulations, initial work on a protocol dashboard, and advancements in formal methods through trace verification in Agda.

## Cross-simulation analysis

- Completed a comprehensive analysis of simulations at tag `leios-2025w09`:
  - Refactored the ELT workflow to improve simulation data processing
  - Modified the Rust simulator to generate fixed-size input blocks (IBs) for comparison with Haskell
  - Partially resolved discrepancies in congestion metrics between simulators
  - Developed detailed analyses of:
    - IB generation to receipt elapsed time
    - Time-in-flight over node-to-node links
  - Identified the dual role of network bandwidth and CPU bottlenecks in high throughput congestion.

## Protocol dashboard initiative

- Initiated the design of an interactive protocol dashboard with planned features:
  - Protocol parameter configuration
  - Stake distribution settings
  - Performance visualization:
    - Block arrival efficiency
    - Transaction duplication
    - Leios operation rewards
    - Resource utilization
  - Security metrics visualization:
    - Quorum failure analysis
    - Certificate forgery detection
    - Adversarial block tracking.

## Rust simulation

- Enhanced parallel message handling capabilities:
  - Implemented parallel mini-protocol message transmission
  - Added even bandwidth distribution between mini-protocols
  - Introduced the `simulate-transactions` configuration option
  - Updated simulation output for better Haskell compatibility
  - Improved block visualization for scenarios with high IB counts.

## Formal methods

- Commenced trace verifier development in Agda:
  - Added decidability to Short Leios protocol relational specification
  - Implemented a proof-by-computation approach for execution traces
  - Applied the successful methodology from Streamlet formalization. 
