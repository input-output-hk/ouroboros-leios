---
title: Weekly Summary – August 11, 2025
authors:
- will
tags: [progress, update, weekly, cip, attack-analysis, rust-simulation, haskell-simulation, proposed-leios]
---

This week, the Leios team advanced the Cardano Improvement Proposal (CIP) documentation, conducted comprehensive attack analysis experiments, and continued cross-validation between simulation implementations. The team successfully demonstrated resilience characteristics of proposed Leios under adversarial conditions and refined protocol specification components for the formal CIP submission.

## CIP development progress

The team made substantial progress on the Ouroboros Leios CIP proposal. The draft specification section is now complete except for the network and incentives components. The motivation and abstract sections have been refined for clarity, enhancing the document's accessibility and technical precision. The first of four main rationale subsections has been fully drafted, providing evidence-based arguments for the necessity and viability of the proposed Leios protocol enhancement.

## Attack resistance analysis

### Initial adversarial simulation experiments

The team conducted the [first simulation experiment for attacks](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w33/analysis.ipynb), examining late Endorser Block (EB) and transaction diffusion scenarios where adversaries control timing of critical protocol messages. The experiment varied the diffusion parameter L_diff and EB propagation schemes to assess protocol robustness under different adversarial strategies.

Key findings from the initial attack analysis include successful demonstration that late-release attacks can impact proposed Leios throughput under specific conditions. The analysis revealed that transaction loss occurred in some scenarios due to memory pool rule formulations in the simulator, leading to important insights for protocol hardening and implementation requirements.

## Cross-simulation validation

### Haskell versus Rust comparison

The team completed another comprehensive comparison between Haskell and Rust simulation implementations at [analysis/sims/202532b](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/202532b). Results indicate successful resolution of previous discrepancies in vote diffusion behavior between the two simulation environments. This validation ensures both implementations produce consistent results for protocol analysis and strengthens confidence in the simulation-based evidence supporting the CIP.

### CIP figure preparation

The [experiment for draft figures for CIP](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/cip/) progressed with updated simulation runs designed to generate publication-quality performance charts and protocol behavior visualizations for inclusion in the formal CIP documentation.

## Next steps

- Complete the remaining network and incentives sections of the CIP specification
- Conduct follow-up analysis on attack experiment findings to refine protocol parameters
- Continue refinement of memory pool rules based on adversarial scenario insights
- Finalize CIP figures and supporting analysis for submission preparation.
