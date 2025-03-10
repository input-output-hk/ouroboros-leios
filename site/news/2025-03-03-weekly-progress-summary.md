---
title: Weekly Summary - 2025-03-03
authors:
- will
tags: [progress, update, weekly]
---

## High-level summary

This week in Leios development, the team focused on simulation analysis, formal methods, and documentation updates. Key accomplishments include in-depth analysis of simulations at tag `leios-2025w10`, advancements in formal methods through a working trace verifier, and development of technical reports.

## Cross-simulation analysis

- Completed a comprehensive analysis of simulations at tag `leios-2025w10`:
  - Analyzed Haskell simulation performance with and without accounting for CPU usage
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
    - Resource utilization in network traffic

## Protocol and formal methods

- Commenced trace verifier development in Agda:
  - Parsing event traces using the Haskell module `leios-trace-hs`

## Documentation and research

- Full draft of the [Leios Technical Report #1](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/technical-report-1.md)
- Skeletal [draft of Leios CIP](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/leios-cip-draft.md) (Consensus-Improvement Proposal)
- Conformed to the latest template for CIPs
- Developed a [detailed analysis of simulations](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w10/analysis.ipynb) for the 100-node Leios network

## Programming and testing

- Resolved several simulation issues:
  - [#235: RB size does not reflect the presence of a certificate?](https://github.com/input-output-hk/ouroboros-leios/issues/235)
  - [#234: Fast transmission of large blocks at moderate IB rate?](https://github.com/input-output-hk/ouroboros-leios/issues/234)
  - [#232: Monotonicity of EB inclusion in RBs?](https://github.com/input-output-hk/ouroboros-leios/issues/232)
  - [#230: EB's not large enough to include their IBs?](https://github.com/input-output-hk/ouroboros-leios/issues/230)
  - [#229: Rust simulations panics from overflow](https://github.com/input-output-hk/ouroboros-leios/issues/229)
- Enabled the visualization of network traffic and logging messages for multiple predefined "scenarios" instead of a single hard-coded trace
- Updated the visualization to display resource utilization in network traffic

## Rust simulation visualization

- Improved visualization capabilities:
  - Added support for multiple predefined "scenarios" instead of single hard-coded trace
  - Moved visualization logic to client-side web worker for better performance
  - Added visualization of per-node network traffic breakdown by message type
- Fixed critical simulation bugs:
  - Resolved issue [#229](https://github.com/input-output-hk/ouroboros-leios/issues/229) causing time travel and crashes in high-traffic high-latency scenarios
