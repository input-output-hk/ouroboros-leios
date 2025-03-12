---
sidebar_position: 4
---

# Resources

This page provides a collection of resources on Ouroboros Leios, including
technical papers, presentations, and videos.

## Technical documentation

### Leios CPS

- [Leios CPS](https://github.com/cardano-foundation/CIPs/blob/master/CPS-0018/README.md)

#### Summary:

- Cardano’s mainnet periodically faces congestion, with block utilization
  exceeding 90%, delaying transactions and impacting user experience, especially
  for use cases like airdrops, DEXes, oracles, and DApps. As new applications
  and bridges (e.g., Cardano-Midnight, Cardano-Bitcoin) increase demand, current
  throughput (~12 TPS max) lags far behind competitors like Solana (7229 TPS).
  In Ouroboros Praos, security constraints (e.g., 5-second block relay within a
  20-second slot) limit block size and script execution, underutilizing network
  resources. This CPS calls for research into scaling solutions like Ouroboros
  Leios to boost transaction volume, size, and execution units, while ensuring
  predictable processing times for time-sensitive applications. Goals include
  defining stakeholder needs, safely increasing limits, and leveraging underused
  resources—all without compromising security or raising node costs. Historical
  data shows frequent near-full blocks and Plutus execution bottlenecks,
  underscoring the urgency as Cardano aims for nation-state-scale usage by 2030.

### Leios CIP

- [Leios CIP](https://github.com/cardano-foundation/CIPs/pull/379)

#### Summary

- – the Cardano Improvement Proposal by Duncan Coutts,
- CIP-0079, proposed by Duncan Coutts in November 2022, introduces Ouroboros
  Leios as a long-term solution to boost Cardano’s transaction throughput beyond
  the limitations of Ouroboros Praos. This CIP provides the rationale and a
  high-level design of the protocol.

### Leios Research Paper

- [High-Throughput Blockchain Consensus under Realistic Network Assumptions](https://iohk.io/en/research/library/papers/high-throughput-blockchain-consensus-under-realistic-network-assumptions/)

#### Summary

- The original research defining the core protocol and its theoretical
  properties. Published on May 31, 2024, by Sandro Coretti, Matthias Fitzi,
  Aggelos Kiayias, Giorgos Panagiotakos, and Alexander Russell, this research
  paper introduces Leios, a blockchain protocol overlay that transforms
  low-throughput permissionless protocols (PoW or PoS) into high-throughput
  systems, achieving near-optimal throughput of (1-δ)σ_H (where σ_H is the
  honest stake fraction and δ>0) under realistic network conditions. Unlike
  prior models assuming unbounded message capacity, Leios addresses adversarial
  tactics like protocol bursts (mass message releases) and equivocations
  (double-signing in PoS) using a freshest-first diffusion network model
  (F_FFD). It employs five key techniques: (i) concurrent Input Block (IB)
  generation for transactions, (ii) Endorser Blocks (EBs) with data availability
  proofs, (iii) a pipelined architecture for uninterrupted processing, (iv)
  freshest-first message prioritization with VRF-based timestamps, and (v)
  equivocation proofs to limit malicious spam. Full Leios ensures throughput
  scales with network capacity, retains base protocol settlement times (adjusted
  by a δ-related constant), and supports dynamic participation, proven secure
  with a stake-based voting scheme using BLS signatures. Applied to Ouroboros,
  Leios offers a scalable, secure layer-1 solution for Cardano, balancing
  throughput, latency, and resilience.

## Videos

- [Scaling Cardano with Leios](https://www.youtube.com/watch?v=Czmg9WmSCcI) –
  Professor Aggelos Kiayias, IO's chief scientist, explains Leios in the context
  of scaling Cardano

- [Understanding Leios](https://www.youtube.com/watch?v=YEcYVygdhzU) – Giorgos
  Panagiotakos, one of the paper's co-authors, provides a detailed explanation
  of the Leios protocol

- **Monthly Leios meetings**:

  - [October 2024](https://drive.google.com/file/d/12VE0__S0knHqXXpIVdXGWvDipK0g89p_/view?usp=sharing)

  - [November 2024](https://drive.google.com/file/d/1W4iu4MwOXILXes1Zi43MeM505KAOHXso/view?usp=sharing)

  - [December 2024](https://drive.google.com/file/d/1F07oKxBgdOEasGcstxEavkPCgr58sbIO/view?usp=sharing)

  - [January 2025](https://www.youtube.com/live/6ovcWDCdqFU?si=-dgnvO7353tUyiDZ&t=120)

## Presentations

- [Leios overview slides](https://docs.google.com/presentation/d/1W_KHdvdLNDEStE99D7Af2SRiTqZNnVLQiEPqRHJySqI/edit?usp=sharing)
  – the presentation by Sandro Coretti-Drayton providing insights into Leios.

- **Monthly Leios presentations**:

  - [October 2024 slides](https://docs.google.com/presentation/d/1KgjJyP6yZyZKCGum3deoIyooYUOretA9W6dTtXv1fso/edit?usp=sharing)

  - [November 2024 slides](https://docs.google.com/presentation/d/11LHQeUuv-TQfiy9GwXkrffSimFjSq8tdTB8qIB-Pk3U/edit?usp=sharing)

  - [December 2024 slides](https://docs.google.com/presentation/d/1LwpcXnXLgrYTSDalJY1SfpeyU_4lIkYhyMy5Kv0Huzw/edit?usp=sharing)

  - [January 2025 slides](https://docs.google.com/presentation/d/1qKXe3CvAvJGVWAssjrKpRrRABMT6I39E1FxUWQ_PZzo/edit?usp=sharing).

## Tools and simulations

- [Throughput simulation](https://www.insightmaker.com/insight/5B3Sq5gsrcGzTD11GyZJ0u/Cardano-Throughput-v0-2)
  – an interactive simulation demonstrating Leios' throughput capabilities.

## Development resources

- [GitHub repository](https://github.com/input-output-hk/ouroboros-leios) – the
  official Leios implementation repository

- [Cost estimator](https://leios.cardano-scaling.org/cost-estimator/) – the tool
  for estimating resource costs in Leios.
