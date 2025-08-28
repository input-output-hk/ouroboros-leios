# Roadmap

This document lays out the vision, mission, strategy and key objectives of the
Leios consensus upgrade for Cardano. It outlines _why_ we are doing this, _how_
we aim to succeed and _what_ we plan to do.

## Vision & mission

Leios supports the vision of Cardano to be known as the best-in-class
blockchain, recognized for performance, reliability, and scalability.
Consequently, our mission is to empower developers, businesses, and communities
by delivering a scalable, reliable, and economically sustainable blockchain
network that fuels innovation and growth.

## Strategy

There are three key pillars to how we approach this project:

- **Technical leadership**: Continuously enhance core protocol and
  infrastructure to achieve and sustain top-tier transaction throughput and
  reliability.
- **Market repositioning**: Publish engaging benchmark results and
  visualizations to overcome any perceptions of capacity limitations.
- **Sustainable decentralisation**: Meet throughput demands, but keep costs low
  and hardware requirements reasonable, to help SPOs stay profitable and
  ultimately preserve market leading levels of decentralization.

<!-- TODO: provide more detail and incorporate more/other principles

- Validate early (as this is novel work)
- Continously deliver (value to the community)
- Transparency to ensure acceptance (decentralized governance)

-->

<!-- TODO KPIs
Several key performance indicators (KPI) will help us guide our design and
measure progress along the way:

### Performance

- **Data throughput**: The amount of transactions the system can process measured by transaction bytes per second (TxB/s) added to the ledger.
- **Script throughput**: Amount of computation that can be done on transactions measured by possible script execution units.
- **Inclusion latency**:: The time it takes for a transaction to reach the ledger in times of high and low demand.

### Efficiency
### Security
### Decentralization
### Adoption
### Sustainability
### Future-proofing
-->

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
