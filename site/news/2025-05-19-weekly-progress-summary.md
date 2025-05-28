---
title: Weekly Summary – May 19, 2025
authors:
- will
tags: [progress, update, weekly]
---

This week, the Leios team focused on improving simulation capabilities, enhancing transaction processing, and expanding the test coverage. The team also made significant progress in addressing transaction inclusion rates and developing a comprehensive conformance testing framework.

## Simulation improvements

### Rust simulation
- Investigated and addressed poor transaction inclusion rates
- Implemented 'late IB inclusion' extension to Full Leios, significantly improving transaction ledger inclusion odds
- Identified and addressed issues with non-sharded input transactions causing excessive duplication
- Made several key enhancements:
  - Enabled late IB inclusion by default
  - Fixed the off-by-one error in late IB inclusion logic
  - Added `praos-fallback-enabled` setting for throughput investigation
  - Improved transaction deduplication in Praos blocks.

## Testing framework

### Conformance testing
- Developed a comprehensive catalog of [potential conformance tests](https://github.com/input-output-hk/ouroboros-leios/blob/main/leios-trace-verifier/conformance-coverage.md)
- Implemented a property-based testing suite for trace verification
- Added both positive and negative test cases covering:
  - Genesis slot operations
  - Block production (RB, IB, EB)
  - Vote generation
  - Various production patterns (sporadic, noisy)
  - Invalid scenarios (equivocation, gaps)
- Successfully verified golden traces against the Agda specification.

## Documentation

### Formal specification
- Launched comprehensive web-based documentation for the Ouroboros Leios formal specification at [leios.cardano-scaling.org/formal-spec](https://leios.cardano-scaling.org/formal-spec/)
- Enhanced documentation features:
  - Interactive exploration of Leios modules
  - Type linking between related components
  - Full text search capabilities
  - Improved accessibility of formal specification details.

## Transaction lifecycle analysis

- Conducted detailed analysis of transaction processing efficiency
- Generated a cumulative probability model for transaction ledger inclusion
- Analyzed the relationship between IB production rate and stage length
- Created visualization of [transaction-to-block inclusion probabilities](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/tx-to-block-cum-slots-fig.svg).

![transaction-to-block inclusion probabilities](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/refs/heads/main/analysis/tx-to-block-cum-slots-fig.svg)

## Next steps

- Continue monitoring and optimizing transaction inclusion rates
- Expand conformance test coverage as the Agda specification evolves
- Further investigate transaction sharding strategies
- Refine transaction lifecycle model based on simulation results.
