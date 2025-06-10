---
title: Weekly Summary – June 3, 2025
authors:
- will
tags: [progress, update, weekly, ci, formal-methods, pseudo-mainnet, topology, rust-simulation, conflicts, incentives, mainnet-scale]
---

This week, the Leios team focused on infrastructure improvements, formal methods advancement, and large-scale network simulation. The team successfully resolved outstanding CI issues, enhanced the formal specification with Full-Short Leios support, and began simulating a realistic 10,000-node pseudo-mainnet topology.

## Infrastructure improvements

- Fixed outstanding CI bugs [#368](https://github.com/input-output-hk/ouroboros-leios/issues/368) and [#379](https://github.com/input-output-hk/ouroboros-leios/issues/379), enabling all CI checks to pass.

## Formal methods advancement

- Added Full-Short Leios as a special case of Short Leios to the [formal specification](https://github.com/input-output-hk/ouroboros-leios-formal-spec/tree/yveshauser/full-short-leios)
- Implemented trace verification capabilities for Full-Short Leios.

## Pseudo-mainnet topology simulation

- Designed and initiated comprehensive simulations for 1 through 300 TPS using the new [pseudo-mainnet topology](https://github.com/input-output-hk/ouroboros-leios/blob/main/data/simulation/pseudo-mainnet/)
- Created a realistic 10,000-node network with:
  - 2,657 block producers and 7,343 relay nodes
  - Realistic stake distribution and geographic distribution
  - Two relays per block producer with realistic latencies
  - 298,756 total connections with 6-hop network diameter
- Observed significant performance challenges with large-scale simulation:
  - Rust simulation: 6 minutes of network time in 10 hours at 1 TPS
  - Performance degradation at higher TPS rates (1 minute network time in 10 hours at 300 TPS)
  - Haskell simulation requires optimization for practical large-network analysis.

## Rust simulation enhancements

- Implemented random sampling of transactions from the Leios memory pool to ensure different IBs contain different transactions when possible
- Added simulation support for Leios variant where IBs contain transaction references rather than full transaction bodies
- Enhanced transaction handling for high-traffic scenarios.

## Analysis of conflicts and incentives

- Completed comprehensive analysis of transaction conflicts, ledger design, and fee incentives
- Key findings on conflict management:
  - Honest duplicates and conflicts are unavoidable with local sortition
  - Memory pool rules can minimize conflicts through prompt transaction removal
  - Collateral requirements for failed transactions conflict with Cardano's guarantees
- Identified block producer compensation strategies for handling conflicting transactions
- Proposed EB-level optimization through bitmap-based transaction validation to reduce persistent storage of duplicates and conflicts.

