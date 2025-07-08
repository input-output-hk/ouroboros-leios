---
title: Weekly Summary – July 1, 2025
authors:
- will
tags: [progress, update, weekly, high-throughput, attack-analysis, rust-simulation, trace-verification, performance-optimization]
---

This week, the Leios team achieved a significant milestone by successfully demonstrating protocol viability at 1,000 TPS, completed comprehensive attack surface analysis, and made substantial improvements to simulation and verification tools.

## High-throughput demonstration

- Successfully completed a 1,000 TPS experiment using basic 300-byte non-Plutus transactions
- Demonstrated the viability of Leios protocol operation at extremely high throughput levels
- Validated protocol performance under stress conditions significantly beyond current Cardano capacity
- Documented detailed findings in the [1000 TPS analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w27/analysis.ipynb).

## Security analysis

- Completed comprehensive attack surface analysis for the second technical report
- Defined terminology and taxonomy for potential Leios attack vectors
- Categorized major attack types and their potential impacts on protocol security
- Enhanced understanding of protocol vulnerabilities and mitigation strategies.

## Rust simulation enhancements

- Finished implementing support for input block (IB) equivocations in the simulation
- Added capability to model and analyze protocol behavior under adversarial conditions
- Enhanced simulation fidelity for security-related protocol testing.

## Trace verifier performance optimization

- Achieved 3x performance improvement by configuring minimum heap size to 1GB
- Reduced garbage collection overhead from 75% to 2% of execution time
- Enhanced profiling capabilities with detailed performance analysis tools
- Improved verification efficiency for large-scale simulation trace analysis.

## Protocol convergence for CIP

- Intensified efforts to converge on a specific Leios variant for the Cardano Improvement Proposal (CIP)
- Applied systematic evaluation methodology to rank protocol candidates from multiple angles
- Evaluated efficiency metrics including temporal efficiency versus storage optimization trade-offs
- Assessed attack surface and security vectors across different protocol variants
- Analyzed utility factors including quality of service, developer friendliness, user experience, and downstream ecosystem impacts
- Focused on eliminating candidates through evidence-based assessment of valuable protocol characteristics.
