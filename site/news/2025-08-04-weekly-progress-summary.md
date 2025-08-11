---
title: Weekly Summary – August 4, 2025
authors:
- will
tags: [progress, update, weekly, cip, plutus, simulation-analysis, linear-leios, haskell-simulation, rust-simulation]
---

This week, the Leios team made significant progress on the Cardano Improvement Proposal (CIP) documentation, conducted extensive Plutus validation experiments, and resolved outstanding discrepancies between simulation implementations. The team successfully demonstrated Linear Leios performance under various Plutus workloads and completed comprehensive protocol parameter analysis for CIP inclusion.

## CIP development progress

The team completed substantial portions of the Leios CIP draft, bringing it closer to submission readiness. The specification section is now complete except for network and incentives components, with the motivation and abstract refined for clarity. The first of four main rationale subsections has been fully drafted, providing evidence-based arguments for Leios necessity and viability.

## Plutus validation experiments

The team conducted comprehensive experiments examining Linear Leios performance under varying Plutus computation loads using 6-vCPU nodes at 100 TPS. Key findings from the [Plutus validation analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w31c/analysis.ipynb) include:

- Linear Leios successfully supported doubling the Plutus per-transaction budget
- Protocol breakdown occurred at sixfold increases in Plutus budgets due to validation bottlenecks
- Endorser blocks could handle approximately 5,000 execution steps of Plutus computation, representing 250 times the current Praos per-block budget
- This capacity could support either a handful of transactions with 20x greater Plutus budgets or increasing every Plutus transaction budget by 50%
- Late diffusion of Plutus-heavy transactions poses potential risks to EB adoption timing.

The analysis revealed significant variability in CPU time requirements for Plutus scripts relative to their execution steps, highlighting the need for careful resource planning in high-throughput scenarios.

## Simulation improvements and comparisons

### Cross-simulation validation

The team completed another comprehensive comparison between Haskell and Rust simulations at [analysis/sims/202532b](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/202532b), successfully resolving previous discrepancies in vote diffusion behavior. This validation ensures both simulation implementations produce consistent results for protocol analysis.

### Protocol parameter optimization

The [2025w32 experiment](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w32/) established a comprehensive set of protocol parameters and throughput scenarios for inclusion in the CIP Evidence section:

- **Protocol variant**: Linear Leios with conservative resource allocation
- **Resource requirements**: 4 vCPU per node, 10 Mb/s bandwidth  
- **Stage configuration**: 7 slots each for voting and diffusion stages
- **Block limits**: Maximum 12 MB transaction references per EB
- **Transaction size**: 1,500 bytes per transaction with normal Plutus frequency

Key performance findings demonstrate that modest computational resources adequately support throughput up to 0.3 TxMB/s, with 7-slot stages providing sufficient diffusion time while minimizing EB discard probability. The 12 MB EB limit allows occasional peak utilization to compensate for unlucky sortition periods.

## Implementation enhancements

### Haskell simulation

The team addressed head-of-line blocking issues in Linear Leios by implementing message slicing capabilities in the mini-protocol multiplexer, eliminating unexpected delays in vote diffusion. Additional work focused on developing new mini-protocols for enhanced Linear Leios simulation fidelity, with ongoing refinements to balance protocol granularity and sophistication.

### Rust simulation

Implementation of transaction withholding attack scenarios for Linear Leios, where EB producers delay transaction publication until EB release. The simulation also received updates to improve handling of late transactions, EBs, and RBs in Linear Leios scenarios.

## Next steps

- Complete remaining network and incentives sections of the CIP specification
- Finalize mini-protocol designs for enhanced simulation accuracy  
- Continue investigation of mempool rule adequacy for high-throughput scenarios
- Expand Plutus validation analysis to cover additional execution budget scenarios.
