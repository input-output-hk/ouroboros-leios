# Roadmap

This document lays out the vision, mission, strategy and key objectives of the
Leios consensus upgrade for Cardano. It outlines _why_ we are doing this, _how_
we aim to succeed and _what_ we plan to do.

## Vision & Mission

Leios supports Cardano’s vision to be recognized as the _best-in-class_ blockchain, renowned for performance, reliability, and scalability.

Our mission is to drive **greater adoption** of the Cardano network by building a blockchain that is:

- *Scalable and reliable*, enabling innovation and sustainable growth for developers, businesses, and communities.

- *Economically sustainable*, ensuring long-term viability and trust, so that projects choose Cardano as the natural home for decentralized applications and enterprise solutions.

This mission positions Leios as the engine powering Cardano’s global impact.

### Strategy

To fulfil our mission, Leios will pursue a strategy built on three pillars:

- **Technical leadership**

  We will continuously advance Cardano’s core protocol and supporting infrastructure to deliver world-class performance. This means investing in innovations that raise transaction throughput, reduce latency, and strengthen network resilience. By setting the technical benchmark in both research and implementation, Leios will ensure Cardano remains at the forefront of blockchain platforms.

- **Market repositioning**

  Beyond technical progress, we will reposition Cardano in the marketplace as a blockchain capable of handling the most demanding use cases. By publishing transparent benchmarks, compelling visualizations, and a clear roadmap of improvements, we can shift perceptions about scalability and reliability. This narrative will attract developers, businesses, and enterprises looking for a secure and future-proof platform.

- **Sustainable decentralization**

  Scaling the network must not come at the cost of centralization. Our strategy ensures throughput grows while hardware requirements remain reasonable, so that Stake Pool Operators (SPOs) can remain profitable and engaged. By keeping operational costs sustainable _relative_ to on-chain revenues, we preserve one of Cardano’s greatest strengths—its unmatched decentralization. A healthy, diverse SPO ecosystem guarantees resilience, fairness, and long-term trust.

### Principles

These are the guiding principles we aim to uphold while executing our strategy, ensuring that our actions align with both our mission and the expectations of the Cardano community.

- **Validate early**

  Because Leios is pioneering novel work, it is essential that ideas and technical approaches are tested and validated as early as possible. This reduces risk, encourages experimentation, and ensures that what we build is not only theoretically sound but also practically viable. Early validation allows the community and stakeholders to give feedback before changes become costly or disruptive, and gives us the opportunity to validate assumptions as early as possible in case the design needs to be adjusted, underlying architectures revised, or implementations adapted.


- **Continuously deliver**

  Progress must be visible and tangible. By continuously delivering value to the community—whether through incremental improvements, new features, marketing content, or learning materials as Leios develops—we build trust and momentum. Frequent delivery demonstrates accountability, keeps developers and the community engaged, and ensures Cardano evolves in step with real user needs.


- **Transparency to ensure acceptance**

  For decentralized governance to flourish, transparency must be at the core of everything we do. Sharing decisions, rationale, data, and results openly not only builds credibility but also empowers the community to participate meaningfully in governance. Clear communication and openness transform stakeholders into active collaborators, ensuring broad acceptance of Leios as a foundation for Cardano’s future.

### Key Performance Indicators (KPIs)

To measure the success of Leios and ensure alignment with our mission, we will track a set of technically rigorous KPIs across performance, efficiency, security, adoption, cost, and scalability. These indicators provide objective evidence of improvements and maintain transparency with the Cardano community, developers, and stakeholders.

#### Throughput and Performance

- **Transaction Data Throughput (TxB/s):** The volume of transaction data (in bytes) successfully processed and added to the ledger per second. This metric provides a more accurate measure of system capacity than raw TPS, as Cardano’s eUTXO model allows transactions to vary in complexity and size.

- **Script Throughput:** The aggregate amount of computation performed on transactions, measured by total script execution units processed per second.
- **Inclusion Latency:** Average time for a transaction to be included in the ledger under both high-demand and low-demand conditions.

- **Block Propagation Time:** Duration required for new blocks to be propagated across the network.

- **Transaction Finalization Time:** Time until transactions are considered finalized and economically irreversible.

#### Network Efficiency
- **Resource Utilization:** Reduction in computational and bandwidth overhead per transaction.

- **Synchronization Speed:** Time required for a new node to fully synchronize with the current blockchain state.

- **Endorser Efficiency:** Percentage of transactions endorsed prior to block inclusion.

#### Security and Decentralization

- **Network Participation:** Number of active nodes engaged in endorsement and block production.

- **Consensus Integrity:** Preservation of Ouroboros Praos/Genesis-level security guarantees.

- **Resistance to Attacks:** Absence of vulnerabilities that could compromise availability, consistency, or safety.

#### User and Developer Adoption

- **Wallet and DApp Integration:** Number of wallets and decentralized applications integrated with Leios.

- **User Experience Feedback:** Decrease in complaints regarding transaction delays or network congestion.

- **Stake Pool Adoption:** Percentage of stake pools adopting Leios for transaction processing.

#### Economic and Cost Efficiency

- **Transaction Fee Variability:** Stability or reduction of transaction fees under varying network load.

- **Smart Contract Execution Costs:** Lower average consumption of execution units per Plutus script.

- **Sustainability:** Ability to keep node infrastructure costs balanced relative to on-chain revenues.

#### Scalability and Future-Proofing

- **Capacity for Future Growth:** Ability to maintain low-latency, high-throughput performance as transaction demand rises.

- **Protocol Upgrade Success:** Seamless integration of Leios with existing Cardano infrastructure and tooling without causing network fragmentation.

## Objectives

As also mentioned in the [introduction](./overview.md), Leios is about maturing
a consensus protocol design from a research paper through multiple [software
readiness
levels](https://committees.docs.intersectmbo.org/intersect-technical-steering-committee/technical-roadmap/project-cards-explained/software-readiness-level)
and ultimately deploy it as a consensus upgrade onto the Cardano network.

Following our strategy outlined above, we identified several key objectives
along the way which are roughly in order, but not strictly sequential. Instead,
each will give rise to a list of _marketable features_, which we going to
identify, progress and deliver throughout the whole lifecycle of this project.
These objectives and features make up the actual product roadmap, which we are
going to update and report on every month via [this github
project](https://github.com/orgs/input-output-hk/projects/167).

<!-- TODO: go into more detail on why each objective is important and also what's in scope -->

### Improvement Proposal (CIP)

> As the Cardano community, we want to learn as early as possible about what is proposed to change, so that it can be discussed across various groups and committees, and referenced in later on-chain governance.

Create a Cardano Improvement Proposal (CIP) that addresses the [Cardano Problem Statement (CPS) about Greater Transaction Throughput (CPS-18)](https://github.com/cardano-scaling/CIPs/blob/master/CPS-0018/README.md). The proposed protocol design shall be applicable to Cardano and feasibility is proven by relevant analysis and simulations.

### Technical specification

> As a node developer, I want to understand in detail how the Leios protocol works and whether my node implementation is correct.

Create design documents, formal specifications and conformance test suites usable by developers of all relevant Cardano node implementations.

### Showcase 1k TPS

> As a potential builder, I want to experience the capability of the proposed consensus upgrade and be convinced that it is as secure as claimed.

Demonstrate 200 TkB/s in a controlled environment using a network prototype, but also validate any assumptions and threat mitigations.

### Leios testnet

> As an SPO and Cardano developer, we want a dedicated network for testing and measuring the perfomance of Leios, so that we can update relevant infrastructure and ensure it can handle increased throughput reliably without compromising security.

A larger scale public network that can be used to validate parameter selection, continuous load tests and allow everyone to integrate with Leios changes.

### Hard fork

> As an SPO and dRep, we want to have a mature Cardano node implementation that enables Leios and have it made available to all users of Cardano.

Create a `cardano-node` release candidate and mature the feature set through `preview`, `preprod` and eventually enable it with a hard-fork on `mainnet`.
