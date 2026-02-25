# Roadmap

Leios focuses on maturing a consensus protocol design from a research paper through multiple [software readiness
levels](https://committees.docs.intersectmbo.org/intersect-technical-steering-committee/technical-roadmap/project-cards-explained/software-readiness-level), and ultimately deploying it as a consensus upgrade on the Cardano network.

## Objectives

Following our [strategy](./strategy.md)￼, several key objectives were identified. These are broadly ordered, but not strictly sequential. Each objective gives rise to a set of marketable features that will be defined, developed, and delivered throughout the project lifecycle.

Together, these objectives and features form the product roadmap, which will be updated and [reported on monthly](./development/monthly-reviews.md) via this [GitHub project](https://github.com/orgs/input-output-hk/projects/167)￼.

<a href="https://github.com/orgs/input-output-hk/projects/167">

![](./roadmap-preview.png)

</a>

### Cardano Improvement Proposal (CIP)

> As a community, Cardano participants seek early visibility into proposed changes so they can evaluate, discuss, and reference them in subsequent on-chain governance decisions.

To address the [Cardano Problem Statement (CPS-18)](https://github.com/cardano-scaling/CIPs/blob/master/CPS-0018/README.md) on greater transaction throughput￼, a Cardano Improvement Proposal (CIP) should define a protocol design applicable to Cardano, with feasibility demonstrated through analysis and simulation.

Publishing a CIP is the standard mechanism for proposing and reviewing protocol changes. It sets out the motivation, specification, and rationale for modifications to the Cardano consensus protocol. Open discussion helps identify blind spots, surface risks, and gather community feedback or support. Supporting evidence, including simulation results and cost analysis, builds confidence in the feasibility and informs governance decisions required to implement the upgrade through a hard fork.

#### Scope

- Refine the protocol design [published by research](https://eprint.iacr.org/2025/1115.pdf) into concrete, implementable variants
- Develop simulators to empirically evaluate protocol variants and explore trade-offs
- Conduct cost analysis and threat modeling
- Propose a CIP to address CPS-18 in the [Cardano Foundation CIP repository](https://github.com/cardano-foundation/CIPs)
- Discuss feedback publicly and incorporate revisions into the CIP.

This work is a joint effort between the innovation and engineering teams at Input Output. 

### Technical specification

> As a node developer, I want to understand in detail how the Leios protocol works and verify that my node implementation is correct.

Produce comprehensive design documents, formal specifications, and conformance test suites for developers of all relevant Cardano node implementations.

Leios introduces a new consensus protocol and therefore requires a precise technical specification to ensure correct and consistent implementation. This applies to the Cardano node Haskell implementation as well as emerging consensus clients such as `amaru`.

Node diversity strengthens Cardano’s security and resilience. Clear specifications, combined with executable conformance test suites, enable independent teams to validate correctness against a common standard and reduce the risk of consensus divergence.

#### Scope

- Produce node-level design, architecture, and impact analysis documents
- Conduct threat modeling and security analysis
- Develop formal specifications in Agda or a comparable formal methods framework
- Deliver conformance test suites that enable node developers to verify correctness
- Participate in node diversity workshops and contribute to the `cardano-blueprint` project.

### Showcase 1k TPS

> As a potential builder, I want to experience the capability of the proposed consensus upgrade and assess whether it meets its security claims.

Demonstrate 200 TkB/s in a controlled network prototype, while validating underlying assumptions and threat mitigations.

A key milestone for Leios is to demonstrate an order-of-magnitude increase in throughput, targeting 200 TkB/s, in a real network of nodes operating in a controlled environment. This provides measurable evidence of capacity gains and strengthens confidence in both the protocol design and its implementation.

An early prototype that exercises the full network layer also enables validation of design assumptions under realistic conditions. It supports structured adversarial testing, assessment of mitigation strategies, and identification of weaknesses that must be resolved before deployment on a public network.

#### Scope

- Develop a network prototype deployable in a controlled environment
- Demonstrate throughput improvements over Praos using clear visual comparisons
- Conduct early load testing and performance measurements
- Benchmark and optimize transaction validation
- Evaluate adversarial scenarios, including stake-based and network-based attacks
- Perform ΔQ modeling and validate protocol parameter selection
- Develop or integrate required cryptographic primitives and prepare them for audit
- Confirm and document required changes across key system components.

### Leios testnet

> As an SPO and Cardano developer, we want a dedicated network to test and measure Leios' performance, so we can update infrastructure and confirm it handles increased throughput without compromising security.

Establish a larger-scale public test network to validate parameter selection, conduct continuous load testing, and support ecosystem integration with Leios.

Although Leios introduces limited structural changes, it modifies consensus and therefore warrants early deployment on a dedicated testnet. A public Leios network would provide a realistic environment to validate protocol behavior at scale and under sustained load.

It would enable SPOs, developers, and infrastructure providers to integrate Leios-related changes, assess operational impact, and verify that systems remain reliable under higher throughput. The network would also support large-scale experiments, repeated load tests, and systematic data collection to inform parameter tuning and readiness for mainnet deployment.

#### Scope

- Bootstrap and promote a public testnet dedicated to Leios
- Provide one or more compatible node implementations for the testnet
- Deliver tools and documentation to support SPO and developer integration
- Conduct continuous load testing and performance measurement
- Monitor infrastructure compatibility across the community
- Run large-scale experiments under varying load conditions and parameter configurations.

### Hard fork

> As an SPO and a DRep, we want a mature Cardano node implementation that enables Leios and is available to all Cardano users.

Create a `cardano-node` release candidate and mature the feature set through `preview` and `preprod` environments, and eventually enable it with a hard fork on `mainnet`.
