# Roadmap

Leios is about maturing a consensus protocol design from a research paper
through multiple [software readiness
levels](https://committees.docs.intersectmbo.org/intersect-technical-steering-committee/technical-roadmap/project-cards-explained/software-readiness-level)
and ultimately deploy it as a consensus upgrade onto the Cardano network.

Following our [strategy](./strategy.md), we identified several key objectives
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
