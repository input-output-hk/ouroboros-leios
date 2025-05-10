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
  and bridges (eg, Cardano-Midnight, Cardano-Bitcoin) increase demand, current
  throughput (~12 TPS max) lags far behind competitors like Solana (7229 TPS).
  In Ouroboros Praos, security constraints (eg, 5-second block relay within a
  20-second slot) limit block size and script execution, underutilizing network
  resources. This CPS calls for research into scaling solutions like Ouroboros
  Leios to boost transaction volume, size, and execution units, while ensuring
  predictable processing times for time-sensitive applications. Goals include
  defining stakeholder needs, safely increasing limits, and leveraging underused
  resources — all without compromising security or raising node costs. Historical
  data shows frequent near-full blocks and Plutus execution bottlenecks,
  underscoring the urgency as Cardano aims for nation-state-scale usage by 2030.

### Leios CIP

- [Leios CIP (CIP-0079)](https://github.com/cardano-foundation/CIPs/pull/379) — Cardano Improvement Proposal by Duncan Coutts, November 2022.

**Summary**

CIP-0079 introduces Ouroboros Leios as a long-term solution to raise Cardano
throughput beyond the limits of Ouroboros Praos. The CIP explains the rationale
and provides a high-level protocol design.

### Leios research paper

- [High-Throughput Blockchain Consensus under Realistic Network Assumptions](https://iohk.io/en/research/library/papers/high-throughput-blockchain-consensus-under-realistic-network-assumptions/) (May 31, 2024) — Sandro Coretti, Matthias Fitzi, Aggelos Kiayias, Giorgos Panagiotakos, and Alexander Russell.  

**Summary**

The paper presents Leios, a protocol overlay that transforms low-throughput PoW
or PoS systems into high-throughput chains, achieving near-optimal throughput of
(1 − δ) σ_H (where σ_H is the honest-stake fraction and δ > 0). Leios addresses
adversarial tactics such as message bursts and equivocations via:

1. Concurrent input-block (IB) generation
2. Endorser blocks (EBs) with data-availability proofs
3. A seven-stage pipeline for uninterrupted processing
4. Freshest-first diffusion with VRF-based timestamps
5. Equivocation proofs to cap malicious spam.

Applied to Ouroboros, Leios yields a scalable, secure layer-1 for Cardano while
maintaining settlement guarantees and supporting dynamic participation.


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

  - [January 2025](https://www.youtube.com/live/6ovcWDCdqFU?si=-dgnvO7353tUyiDZ&t=120).

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
