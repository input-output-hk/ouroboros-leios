---
title: Weekly Summary – April 14, 2025
authors:
- will
tags: [progress, update, weekly, haskell-simulation, rust-simulation, mini-protocols, cost-dashboard, transaction-lifecycle, full-leios, network-protocols]
---

This week, the team made substantial progress in both the Haskell and Rust simulations, refined cost estimates, and carried out detailed analyses of the transaction lifecycle and Full Leios simulations.

### Simulation improvements

#### Haskell simulation
- Completed the first draft of new mini protocols for Leios diffusion
  - Modeled protocols after block-fetch and node-to-node transaction submission from `ouroboros-network`
  - Included IB relay, EB relay, and vote relay for header diffusion and body announcements
  - Included IB fetch and EB fetch for body diffusion
  - Worked on the CatchUp protocol for older blocks
  - See `simulation/docs/network-spec` for full protocol details
- Renamed `short-leios` command to `leios` as it now covers the full variant as well
  - `short-leios` is kept as alias for compatibility.

#### Rust simulation
- Fixed conformance issues with the shared trace format
- Fixed a bug in the voting logic that prevented EBs from receiving enough votes to be included on-chain
- Updated visualizations to use smaller trace files in preparation for hosting on the documentation site.

### Revisions to the cost dashboard

The [cost dashboard](https://leios.cardano-scaling.org/cost-estimator/) was updated with lower and more realistic IO estimates.

### Transaction lifecycle analysis

The Jupyter notebook [Analysis of transaction lifecycle](https://github.com/input-output-hk/ouroboros-leios/blob/leios-2025w17/analysis/tx-to-block.ipynb) estimates the delay introduced at each of the seven stages of Full Leios as a transaction progresses from the memory pool to being referenced by a Praos block.

Key findings from the analysis:
1. Reducing stage lengths below 10 slots offers little benefit
2. The number of shards should remain low enough to maintain a high IB rate per shard relative to the stage length
3. Low EB rates result in many orphaned IBs
4. With realistic parameters, the delay from transaction submission to its inclusion in an RB is approximately two minutes.

Potential next steps:
- Translate the model into Delta QSD to capture network effects
- Compare the model's output with results from the Rust simulator
- Extend the model to account for different memory pool and ledger variants under evaluation.

### Simulation and analysis of Full Leios

The team conducted comprehensive simulations using both Haskell and Rust simulators at tag [leios-2025w16](https://github.com/input-output-hk/ouroboros-leios/releases/tag/leios-2025w16). The simulations covered 648 scenarios of Full and Short Leios with varied parameters:

- IB production rate
- IB size
- EB production rate
- Stage length
- CPU constraints.

Two new output files were generated:
1. A summary of network, disk, and CPU resource usage over the course of the simulation
2. The vertices and edges of the Leios graph, showing linkages between transactions, IBs, EBs, RBs, and votes (can be visualized as an interactive web page).

Key findings:
- The Rust and Haskell simulations show generally close agreement
- The Haskell simulation encounters network congestion at 16 IB/s, while the Rust simulation does not
- The Rust simulation consumes more CPU at high IB rates than the Haskell simulation
- In some cases, the Rust simulation does not produce enough votes to certify an EB.

Detailed results are available in the Jupyter notebook [analysis/sims/2025w16/analysis.ipynb](https://github.com/input-output-hk/ouroboros-leios/blob/leios-2025w17/analysis/sims/2025w16/analysis.ipynb). 
