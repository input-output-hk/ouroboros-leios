---
title: Weekly Summary – March 3, 2025 
authors:
- will
tags: [progress, update, weekly]
---

## High-level summary

This week in Leios development, the team focused on simulation analysis, formal methods, and documentation updates. Key accomplishments include in-depth analysis of simulations at tag `leios-2025w10`, advancements in formal methods through a working trace verifier, and the development of technical reports.

## Cross-simulation analysis

- Completed a comprehensive analysis of simulations at tag `leios-2025w10`:
  - Analyzed Haskell simulation performance with and without CPU usage considerations
  - Varying key protocol parameters:
    - IB production rate
    - IB size
    - Length of Leios stages
  - Identified the following aspects of Leios:
    - Delay between IB generation and receipt at nodes
    - Peak and mean CPU usage over time
    - Breakdown of CPU usage by task type
    - Sizes of IBs, EBs, and RBs
    - Duplicate IB references in EBs
    - Reference to EBs from RBs
    - Resource utilization in network traffic.

## Protocol and formal methods

- Began developing a trace verifier in Agda:
  - Implemented event trace parsing using the Haskell module `leios-trace-hs`.

## Documentation and research

- Completed the full draft of the [Leios technical report #1](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/technical-report-1.md)
- Created a skeletal [draft of the Leios CIP](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/leios-cip-draft.md)
- Aligned with the latest CIP template
- Developed a [detailed simulation analysis ](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w10/analysis.ipynb) for the 100-node Leios network.

## Programming and testing

- Resolved several simulation issues:
  - [#235: RB size does not reflect the presence of a certificate](https://github.com/input-output-hk/ouroboros-leios/issues/235)
  - [#234: Fast transmission of large blocks at moderate IB rate](https://github.com/input-output-hk/ouroboros-leios/issues/234)
  - [#232: Monotonicity of EB inclusion in RBs](https://github.com/input-output-hk/ouroboros-leios/issues/232)
  - [#230: EBs are not large enough to include their IBs](https://github.com/input-output-hk/ouroboros-leios/issues/230)
  - [#229: Rust simulations panics from overflow](https://github.com/input-output-hk/ouroboros-leios/issues/229)
- Enabled the visualization of network traffic and logging messages for multiple predefined 'scenarios' instead of a single hard-coded trace
- Updated the visualization to display resource utilization in network traffic.

## Rust simulation visualization

- Improved visualization capabilities:
  - Added support for multiple predefined 'scenarios' instead of single hard-coded trace
  - Moved the visualization logic to the client-side web worker for better performance
  - Added the visualization of per-node network traffic breakdown by message type
- Fixed critical simulation bugs:
  - Resolved issue [#229](https://github.com/input-output-hk/ouroboros-leios/issues/229) causing time travel and crashes in high-traffic high-latency scenarios.
