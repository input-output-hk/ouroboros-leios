---
title: Weekly Summary – June 24, 2025
authors:
- will
tags: [progress, update, weekly, simulation-analysis, variants, sharding, conflict-experiments, bandwidth, spatial-efficiency, temporal-efficiency]
---

This week, the Leios team conducted comprehensive experiments examining protocol variants, conflict handling, and bandwidth requirements. The team completed analysis of nine candidate Leios variants with different sharding strategies, performed detailed conflict experiments at 100 TPS, and validated bandwidth requirements across multiple throughput scenarios.

## Simulation analysis of protocol variants

- Completed comprehensive analysis of nine candidate variants of Leios examining three basic variants and three sharding strategies:
  - Basic variants: Full, Full without IBs, Full with transaction references
  - Sharding strategies: Unsharded, Sharded, Overcollateralized 1x
- Identified significant differences in spatial and temporal efficiencies across variants:
  - Full with transaction references achieved highest spatial efficiency (95.999-96.466%)
  - Full without IBs demonstrated fastest time to ledger (43.052-43.057s)
  - Sharded variants generally showed improved spatial efficiency but increased latency
- Documented detailed findings in the [analysis notebook](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w26/analysis-variants-sharding.ipynb).

![Spatial efficiency of nine Leios variants](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/main/analysis/sims/2025w26/plots/vars/spatial-efficiency.svg)

![Temporal efficiency of nine Leios variants](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/main/analysis/sims/2025w26/plots/vars/reach-rb-tx.svg)

## Conflict experiments

- Conducted experiments exploring the effect of conflicting transactions at 100 TPS using the simplest Leios variant
- Tested scenarios with 0%, 25%, and 50% of transactions conflicting with other transactions
- Key findings from the [conflict analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w26/analysis.ipynb):
  - Spatial efficiency can be as low as 55% due to occasional IB production before previous reception
  - All non-conflicted transactions reach the ledger within 75 seconds
  - NIC bandwidth of 20 Mb/s is sufficient for protocol operation
  - Four vCPU cores provide adequate processing capacity
  - Large IBs (up to 2 MB) diffuse globally within 5 seconds
  - IB traffic does not interfere with other protocol message types.

![Mean nodal network ingress at 100 TPS](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/main/analysis/sims/2025w26/plots/cxs/ingress-average-area.png)

![Diffusion of IBs at 100 TPS](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/main/analysis/sims/2025w26/plots/cxs/elapsed-IB.png)

## Bandwidth experiments

- Completed experiments exploring bandwidth limitations at 100 TPS and 300 TPS documented in the [bandwidth analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w25/analysis.ipynb)
- Validated protocol parameters for high performance: mini-mainnet topology, 1-2 IB/s, 10 slot/stage, 328 kB/IB maximum, 1.5 EB/stage, and multiple shards
- Key performance findings:
  - Achieved 80% spatial efficiency across tested scenarios
  - All transactions reach the ledger within two minutes
  - 30 Mbps NIC bandwidth is sufficient for Leios node operation
  - Four-core vCPU provides adequate processing capacity
  - Results insensitive to inter-nodal link bandwidths above 50 Mb/s
  - Even 10 Mb/s links show minimal impact on protocol performance.

![Diffusion of IBs at 300 TPS by link bandwidth](https://raw.githubusercontent.com/input-output-hk/ouroboros-leios/main/analysis/sims/2025w25/plots/bw-2IBps/elapsed-IB.png)

## Rust simulation improvements

- Added support for IB equivocation (work in progress, evaluating impact)
- Implemented minor usability improvements to the CLI tool
- Added sharding support to the 'full without IBs' variant of Leios.


## CDDL Version 1

- finalized and merged a first version of the CDDLs for the current variants in discussion for CIP, here in [PR-396](https://github.com/input-output-hk/ouroboros-leios/pull/396/commits/c450c76ce49aae5a35a0d326de73280795e1074e).