---
title: Weekly Summary – April 14, 2025
authors:
- will
tags: [progress, update, weekly]
---

This week, the team achieved significant milestones in both the Haskell and Rust simulations, improved cost estimates, and conducted comprehensive analyses of transaction lifecycle and Full Leios simulations.

### Simulation improvements

#### Haskell simulation
- Completed first draft of new mini protocols for leios diffusion
  - Protocols modeled after BlockFetch and node-to-node Tx-Submission from ouroboros-network
  - IB-relay, EB-relay, Vote-relay for header diffusion and body announcements
  - IB-fetch, EB-fetch for body diffusion
  - CatchUp protocol for older blocks
  - See `simulation/docs/network-spec` for complete protocol details
- Renamed `short-leios` command to `leios` since it now covers full variant as well
  - `short-leios` is kept as alias for compatibility

#### Rust simulation
- Fixed conformance with shared trace format
- Fixed bug with voting logic which was preventing EBs from receiving enough votes to get on-chain
- Updated visualization to use smaller trace files to prepare for hosting on docs site

### Revisions to cost dashboard

The [cost dashboard](https://leios.cardano-scaling.org/cost-estimator/) was updated with lower and more realistic IO estimates.

### Analysis of transaction lifecycle

The Jupyter notebook [Analysis of transaction lifecycle](https://github.com/input-output-hk/ouroboros-leios/blob/leios-2025w17/analysis/tx-to-block.ipynb) estimates the delay imposed by each of the seven stages of Full Leios as a transaction moves from memory pool to being referenced by a Praos block.

Key findings from the analysis:
1. There seems little advantage to moving to stage lengths less than 10 slots
2. The number of shards should be kept small enough so that the IB rate per shard is high relative to the stage length
3. Low EB rates result in many orphaned IBs
4. Realistic parameter settings result in an approximately two-minute delay between transaction submission and its referencing by an RB

Potential next steps:
- Translating this model into Delta QSD to include network effects
- Comparing this model's results to output of the Rust simulator
- Elaborating the model to represent the memory-pool and ledger variants under consideration

### Simulation and analysis of Full Leios

The team conducted comprehensive simulations using both Haskell and Rust simulators at tag [leios-2025w16](https://github.com/input-output-hk/ouroboros-leios/releases/tag/leios-2025w16). The simulations covered 648 scenarios of Full and Short Leios with varied parameters:
- IB production rate
- IB size
- EB production rate
- Stage length
- CPU constraints

Two new output files were generated:
1. Summary of network, disk, and CPU resource usage over the course of the simulation
2. Vertices and edges of the "Leios graph" showing linkages between transactions, IBs, EBs, RBs, and votes (can be visualized as an interactive web page)

Key findings:
- Agreement between Rust and Haskell simulations is generally quite close
- The Haskell simulation experiences network congestion at 16 IB/s, but the Rust simulation does not
- The Rust simulation uses more CPU at high IB rates than the Haskell simulation
- The Rust simulation sometimes does not produce enough votes to certify an EB

Detailed results are available in the Jupyter notebook [analysis/sims/2025w16/analysis.ipynb](https://github.com/input-output-hk/ouroboros-leios/blob/leios-2025w17/analysis/sims/2025w16/analysis.ipynb). 