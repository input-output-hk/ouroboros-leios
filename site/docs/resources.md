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

- Cardano's mainnet periodically faces congestion, with block utilization
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

- [Monthly review videos](./development/monthly-reviews.md) – recordings and presentations from our monthly public review meetings

## Presentations

- [Leios overview slides](https://docs.google.com/presentation/d/1W_KHdvdLNDEStE99D7Af2SRiTqZNnVLQiEPqRHJySqI/edit?usp=sharing)
  – the presentation by Sandro Coretti-Drayton providing insights into Leios.

## Tools and simulations

- [Throughput simulation](https://www.insightmaker.com/insight/5B3Sq5gsrcGzTD11GyZJ0u/Cardano-Throughput-v0-2)
  – an interactive simulation demonstrating Leios' throughput capabilities.

## Development resources

- [GitHub repository](https://github.com/input-output-hk/ouroboros-leios) – the
  official Leios implementation repository

- [Cost estimator](https://leios.cardano-scaling.org/cost-estimator/) – the tool
  for estimating resource costs in Leios.


## Leios Comparisons and Analyses

- [Leios Scorecard Comparison](leios-comparison.md) – How does Cardano’s Ouroboros Leios stack up against Solana, Ethereum, and Bitcoin? This scorecard compares throughput, fees, decentralization, and more.

- [Leios Use Cases](leios-use-cases.md) – Discover how Ouroboros Leios, Cardano’s next-gen protocol, could enable unique use cases like global microtransactions, supply chain tracking, and more, outshining other blockchains.

- [Leios Node Cost Analysis](leios-cost-analysis.md) – During the April 2025 status meeting, we shared early cost estimates for running Leios nodes. Here’s a straightforward breakdown of those figures, showing what it might cost to operate Leios compared to the current Praos protocol and the potential revenue from transaction fees.

## Leios Monthy Meeting Recaps

Want to catch up on the latest Leios news but can't make the monthly status meeting? No problem! Take a look at our brief meeting recaps to see what was discussed and where the team is headed next!

May 2025 Recap:
<div style={{position: 'relative', paddingBottom: '56.25%', height: 0}}>
  <iframe
    style={{position: 'absolute', top: 0, left: 0, width: '100%', height: '100%'}}
    src="https://www.youtube.com/embed/foBHBGV3DaE?si=SnZI-wYznEV1gIxH"
    title="YouTube video player"
    frameborder="0"
    allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture"
    allowfullscreen
  />
</div>
