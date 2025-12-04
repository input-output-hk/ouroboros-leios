---
title: Leios technical design and implementation plan
status: Draft
version: 0.5
author:
  - Sebastian Nagel <sebastian.nagel@iohk.io>
  - Nicolas Frisby <nick.frisby@iohk.io>
  - Thomas Vellekoop <thomas.vellekoop@iohk.io>
  - Michael Karg <michael.karg@iohk.io>
  - Martin Kourim <martin.kourim@iohk.io>
  - Gamze Orhon Kılıç <gamze.kilic@iohk.io>
  - Hamza Jeljeli <hamza.jeljeli@iohk.io>
---

# Introduction

This technical design document bridges the gap between the protocol-level specification ([CIP-164](https://github.com/cardano-foundation/CIPs/pull/1078)) and its concrete implementation in [`cardano-node`](https://github.com/IntersectMBO/cardano-node). While CIP-164 defines *what* the Leios protocol is and *why* it benefits Cardano, this document addresses *how* to implement it reliably and serve as a practical guide for implementation teams.

This document builds on the [impact analysis](../ImpactAnalysis.md) and [early threat modelling](../threat-model.md) conducted. The document outlines the necessary architecture changes, highlights key risks and mitigation strategies, and proposes an implementation roadmap. As the implementation plan itself contains exploratory tasks, this document can be considered a living document and reflects our current understanding of the protocol, as well as design decisions taken during implementation.

Besides collecting node-specific details in this document, we intend to contribute implementation-independent specifications to the [cardano-blueprint](https://cardano-scaling.github.io/cardano-blueprint/) initiative and also update the CIP-164 specification through pull requests as needed.

**Document history**

This document is a living artifact and will be updated as implementation progresses, new risks are identified, and validation results become available.

| Version | Date       | Author          | Changes                                                            |
|---------|------------|-----------------|--------------------------------------------------------------------|
| 0.5     | 2025-10-29 | Sebastian Nagel | Re-structure and start design chapter with impact analysis content |
| 0.4     | 2025-10-27 | Sebastian Nagel | Add overview chapter                                               |
| 0.3     | 2025-10-25 | Sebastian Nagel | Add dependencies and interactions                                  |
| 0.2     | 2025-10-24 | Sebastian Nagel | Add implementation plan                                            |
| 0.1     | 2025-10-15 | Sebastian Nagel | Initial draft                                                      |

# Overview

Cardano as a cryptocurrency system fundamentally relies on an implementation of Ouroboros, the consensus protocol (TODO cite praos and genesis papers), to realize a permissionless, globally distributed ledger. The consensus protocol provides two essential properties that underpin Cardano's value proposition: **persistence** ensures immutability of confirmed transactions, while **liveness** guarantees that new valid transactions will be included. These properties enable secure and censorship-resistant transfer of value, as well as the execution of smart contracts in a trustless manner.

Ouroboros Leios introduces **high-throughput** as a third fundamental property, extending the currently deployed Ouroboros Praos variant. By enabling the network to process a significantly higher number of transactions per second, Leios addresses the economic scalability requirements necessary to support a growing user base and application ecosystem. This enhancement transforms Cardano from a system optimized for security and decentralization into one that maintains these properties while achieving higher transaction processing capacity demanded by modern blockchain applications.

## From research to implementation

As was the case for the [Praos variant of Ouroboros](https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-design/network-design.pdf#subsection.5.1), the specification embodied in the published and peer-reviewed [research paper for Ouroboros Leios](https://eprint.iacr.org/2025/1115.pdf) was not intended to be directly implementable. Initial research and development studies confirmed this expectation, identifying several unsolved problems with the fully concurrent block production design when considering the concrete Cardano ledger and what consequences this would have (TODO: cite suitable R&D reports, [Tech Report #2](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/technical-report-2.md#conflicts-ledger-and-incentives), [Impact analysis survey](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/ImpactAnalysis.md#full-survey)); further research is needed before those parts can be implemented.

The design presented in [CIP-164](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md), also known as "Linear Leios", focuses on the core insight of utilizing the unused network bandwidth and computational resources during the necessary and eponymous "calm periods" of the Praos protocol. This approach provides an immediately implementable design that can deliver orders of magnitude higher throughput while preserving the security guarantees that make Cardano valuable.

The Linear Leios protocol operates by allowing a second, bigger type of block to be produced in the same block production opportunity. Block producers can produce and announce an endorser block (EB), which endorses additional transactions that would not fit within the Praos block. EBs are distributed through the network and subjected to validation by a committee of stake pools, who vote on their transaction data closure's availability and validity. Only EBs that achieve a high threshold of stake-weighted votes become certified and can be included in the ledger through exclusive anchoring of a certificate in the subsequent block - now called a ranking block (RB). This mechanism allows for significantly higher transaction throughput while maintaining the security properties of the underlying Praos consensus. See the CIP for more details on the protocol specification and rationale itself.

## Cardano node as a real-time system

The implementation of Leios must be understood in the context of the Cardano node as a concurrent, reactive system operating under real-time constraints in an adversarial environment. While "real-time" in this context does not refer to the millisecond-level hard deadlines found in industrial control systems, timely action at the scale of seconds nontheless remains crucial to protocol success and network security. 

The currently deployed Praos implementation establishes clear [data diffusion targets](https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-design/network-design.pdf#subsection.5.1): blocks must reach 95% of nodes within the 5-second $\Delta$ parameter, with target performance at 98% and stretch goals at 99%. While these are comfortably achieved most of the time, blocks are regularly adopted within 1 second across the network, there are some situations even in the current system where the target is not reached. For example, due to reward calculations happening at the epoch boundary.

Despite being hard deadlines, these targets reflect the reality that network vulnerability increases when not being met. The protocol's safety and liveness guarantees depend on honest nodes being able to propagate blocks rapidly enough to prevent adversarial forks from gaining traction. Failure to meet these timing constraints can lead to increased rates of short forks, reduced chain quality, and - if persistent - ultimately compromise the integrity of the ledger. 

## Concurrency and resource management

The current primary responsibilities of a Cardano node are roughly:

- Block diffusion: receiving chains from upstream, validate and select the best chain, and transmit chains downstream.
- Transaction submission: receiving, validating, and transmitting transactions to be included in blocks.
- Block production: creating new blocks and extending current chain when selected as slot leader. 

Despite this apparent simplicity, this already results in a highly concurrent system once cardinalities of upstream and downstream network peers are considered. A `cardano-node` with the default configuration maintains 20 upstream hot peers, 10 upstream warm peers and can have up to a few hundred downstream connections, each of which may be simultaneously requesting or serving data. All of these operations share critical resources, including memory, CPU, and network bandwidth, requiring careful resource management to ensure timing requirements are met even under load.

Concretely, in the current system there are (including protocols for supporting features like peer sharing):

- 2 pipelined + 3 non-pipelined instances per upstream peers => 7 threads per upstream peer;
- 1 pipelined + 4 non-pipelined instances per downstream peer => 6 threads per downstream peer

Leios significantly expands this concurrency model by introducing new responsibilities:

- Endorser block and closure diffusion: receiving, validating, and transmitting EBs and their transaction closures.
- Voting and vote diffusion: receiving, validating, and transmitting own and foreign votes on EBs. 

Given the [proposed Leios mini-protocols](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#leios-mini-protocols), this would result in:

- 4 pipelined + 3 non-pipelined per upstream peers => 11 threads per upstream peer;
- 1 pipelined + 6 non-pipelined per downstream peer => 8 threads per downstream peer

With these two additional functionalities, each across many peers, the node set of concurrent tasks strictly increases. The implementation must ensure that the increased data flows and processing demands do not interfere with each other, or priorization mechanisms ensure to meet the stringent timing constraints necessary for protocol security.

## Designing for the worst-case

Related to the principle of [optimizing for the worst case](https://cardano-scaling.github.io/cardano-blueprint/principles/index.html#optimise-only-for-the-worst-case), the security argument for Leios protocol depends critically on worst-case diffusion characteristics. Endorser blocks and their transaction closures must be "small enough" that the difference between optimistic diffusion (leading to successful certification) and worst-case diffusion remains bounded by the protocol parameter $L_\text{diff}$ according to the [protocol's security argument](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#protocol-security).

If the optimistic, average-case performance is improved with suitable algorithms, data structures and optimizations, but the worst-case scenario is not, more conservative parameter choices would be required to maintain security guarantees. This would negate the anticipated benefits of the optimizations in the first place. Therefore, the implementation must prioritize ensuring that even in adverse network conditions or under attack, the diffusion of EBs and their closures remains within acceptable bounds.

> [!WARNING]
> TODO: the situation is not as dire though, we have some design freedom because strictly less work needs to be done on the worst-case path (e.g. rely on certified validity and cheaply build ledger states instead of validating transactions)

Besides, as with Praos, the enhanced information exchange requirements of Leios must not compromise the system's resilience against denial of service attacks and asymmetric resource consumption attempts. The implementation must maintain defensive properties while supporting the increased data flows and processing requirements that enable higher throughput.

## Implementation imperatives

In summary, the technical design described in subsequent chapters must ensure that nodes continue to operate reactively and meet timing requirements despite increased responsibilities and data volumes. This requires careful bounding of resource usage and sophisticated prioritization mechanisms across concurrent responsibilities.

The complexity of this challenge emphasizes the critical importance of non-functional requirements specification for each component, rigorous performance engineering practices, and continuous benchmark validation throughout the development process. Only through systematic attention to these implementation details can the protocol deliver the security and performance properties that make Leios a valuable enhancement to Cardano's capabilities.

The following chapters detail the specific risks that inform architectural decisions, the concrete technical design that addresses these challenges, and the implementation plan that will deliver a production-ready system.

# Implementation plan

The implementation of Ouroboros Leios represents a substantial evolution of the Cardano consensus protocol, introducing high throughput as a third key property alongside the existing persistence and liveness guarantees. The path from protocol specification to production deployment requires careful validation of assumptions, progressive refinement through multiple system readiness levels, and continuous demonstration of correctness and performance characteristics. This chapter outlines the strategy for maturing the Leios protocol design through systematic application of formal methods, simulation, prototyping, and testing techniques.

The result is an implementation plan that not only covers the ["path to active" of CIP-164](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#path-to-active), but also serves as a rationale for what concrete steps will be taken on our [product roadmap](https://leios.cardano-scaling.org/docs/roadmap/) of realizing Ouroboros Leios.

> [!WARNING]
>
> TODO: mention on-disk storage and its availability; relevant for prototyping and early testnet (chain volume)
>
> TODO: incorporate or at least mention interactions with Peras
>
> TODO: also mention Genesis (potential to only do this later once testnet available?)

## Approach

Research and development of distributed consensus protocols does not follow a linear waterfall process. Rather, the protocol design must be matured through various stages of validation, each building confidence in different aspects of the system. The peer-reviewed research paper provides strong theoretical guarantees under certain assumptions, but translating these guarantees into a working implementation that operates reliably on real-world infrastructure requires bridging substantial gaps. The implementation strategy must therefore balance multiple concerns: validating that core assumptions hold in practice, ensuring that refinements preserve essential properties, building developer confidence through rigorous testing, and ultimately securing acceptance from the governing bodies that must approve deployment to mainnet.

The challenge is compounded by the nature of the system itself. Cardano as deployed on mainnet is a globally distributed system with hard real-time constraints operating in an adversarial environment. Failures or performance degradation cannot be tolerated, as they directly impact the economic value and security guarantees that users depend upon. This necessitates an implementation approach that validates critical properties early, maintains continuous delivery of working prototypes, and ensures transparency in both progress and limitations throughout the development process.

Three [principles](https://leios.cardano-scaling.org/docs/strategy#principles) guide the implementation strategy: First, **early validation** of critical assumptions and risks enables discovery of fundamental problems as early as possible in the development cycle and reduces the likelihood for wasteful pivots and delays in delivery. Second, the implementation must progress through **continuous delivery** of increasingly capable prototypes rather than attempting to build the complete system in isolation. This allows for empirical validation at each stage and enables course corrections based on observed behavior. Third, **transparency** in both capabilities and limitations must be maintained throughout, ensuring that stakeholders including stake pool operators and delegated representatives can make informed decisions about deployment readiness.

These principles are also reflected in the choice of validation techniques applied at each stage. Formal methods provide the strongest guarantees of correctness but apply to abstracted models. Simulation enables exploration of protocol behavior under controlled conditions including adversarial models. Prototypes running on real infrastructure validate that theoretical performance bounds can be achieved in practice. Public testnets demonstrate end-to-end integration and allow the broader community to evaluate the system under realistic conditions.

## Correctness in two dimensions

Formal specification and verification play a central role in ensuring correctness throughout the implementation process, which happens along two dimensions:
- Maturity: Implementations maturing from proof of concept, prototype to production-ready release candidates
- Diversity: Multiple emerging implementations of Cardano nodes using different programming langugages and targeting slightly different use cases

A protocol specification captured in a formal langugage like Agda, provides an unambiguous description of the protocol that can be checked for consistency and allows proving equivalence and other properties. A formal specification serves as the authoritative reference against which all implementations must be verified.

The approach to formal verification in Leios follows the "trail of evidence" methodology successfully applied in previous Ouroboros consensus implementations. Rather than attempting to verify the entire codebase directly, which becomes intractable for systems of this complexity, the methodology establishes correctness through a chain of increasingly refined specifications. For example, the high-level specification defines the protocol abstractly, while further refined specifications would focus on details such as message ordering and timing. Finally, an executable implementation is shown to correspond to the formal specification through a combination of techniques including type safety, property-based testing, and trace verification - often summarized as **conformance testing**.

Trace verification deserves particular attention as it provides a bridge between formal specifications and running code. The approach involves instrumenting both the formal specification and the implementation to produce detailed execution traces. These traces can then be compared to verify that the implementation exhibits the same observable behavior as the specification for given inputs. For consensus protocols, the relevant observable behavior includes the sequence of blocks produced, the certificates generated, and the final ledger state. By systematically exploring the space of possible inputs including adversarial scenarios, high confidence can be achieved that the implementation faithfully realizes the specification.

Multiple implementations provide additional assurance through diversity. The primary Haskell implementation in `cardano-node` continues to serve as the reference, while alternative implementations in other languages are currently in development and will eventually increase the **node diversity** of Cardano. Alternative implementations on the node- or component-level serve multiple purposes:
  - validate that the specification is sufficiently precise and complete,
  - exercise different corner cases that might be missed by a single implementation, and
  - reduce the risk that a subtle bug in one implementation compromises the entire network.

The formal specification must be maintained as a living artifact throughout implementation. As design decisions are made to address practical concerns, these decisions must be reflected back into the specification to ensure it remains accurate. This bidirectional relationship between specification and other steps on the implementation plan is essential. The specification guides implementation, while implementation experience reveals necessary refinements to the specification. Documentation of these refinements and the rationale behind them provides crucial context for future maintainers and for external review. Consequently, the specification itself and other implementation-independent artifacts will be contributed to the [`cardano-blueprint`](https://cardano-scaling.github.io/cardano-blueprint) initiative.

## Simulation and protocol validation

Simulations provide a very controlled environment for exploring protocol behavior before deploying to real infrastructure. Two complementary simulation approaches have been used so far to [validate the proposed protocol in CIP-164](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#simulation-results), each with distinct strengths and even using different implementation languages.

A discrete event simulation implemented in Rust, models Leios message exchanges between nodes, abstracting lower-level details for speed—running orders of magnitude faster than real time to enable statistical analysis over thousands of runs with complete observability and arbitrary adversarial behavior injection. This validates security arguments by systematically exploring protocol behavior under varying loads, expected data diffusion in small to medium sized network topologies, or adversarial scenarios like data withholding, and exploration of protocol parameters before testnet deployment.

Another Haskell-based simulation using IOSim and the actual network framework used in the `cardano-node`. This reduces model-implementation divergence while enabling studies of the dynamic behavior and resource management in detail. While IOSim is used in the existing network and consensus layers through property-based testing, and extends naturally to Leios components, the simulator built from this was not able to scale to large networks.

Both approaches necessarily abstract real system details and thus provide evidence of correct behavior under idealized conditions and suggest workable parameters, but cannot definitively predict real-world performance. Maintaining simulation synchronization with evolving implementation requires discipline, but enables rapid exploration of alternatives, early feature validation, and serves as executable documentation for new developers.

## Prototyping and adversarial testing

Prototypes on real infrastructure validate performance characteristics that simulation typically cannot guarantee. The line between simulation and prototyping is blurry, but both concepts share the trait of allowing rapid exploration of the most uncertain aspects of the design before committing to a full implementation. Referring back to the key threats and assumptions to validate early, the primary focus of prototyping is on network diffusion performance under high throughput conditions and adversarial scenarios.

**Network diffusion prototype:** An early implementation of the actual Leios network protocols and freshest-first delivery mechanisms, that allows running experiments with various network topologies. Ledger validation of Leios concepts is stubbed out and transmitted data is generated synthetically to focus purely on network performance. Deployed to controlled environments like local devnets and private testnets like the the Performance and Testing cluster, this prototype systematically explores how performance scales with network size and block size, tests different topologies, and crucially answers whether the real network stack achieves the diffusion deadlines required by protocol security arguments. Key measurements include endorser block arrival time distributions, freshest-first multiplexing effectiveness, topology impact on diffusion, and behavior under adversarial scenarios including eclipse attempts and targeted withholding. These measurements will answer questions like, "how much" freshest-first delivery we need, whether the proposed network protocols are practical to implement and what protocol parameter are feasible.

Adversarial testing represents a crucial aspect of prototype validation. In a controlled environment, some nodes can still be configured to exhibit adversarial behaviors such as sending invalid blocks, withholding information, or attempting to exhaust resources of honest nodes. Observing how honest nodes respond provides evidence that the mitigations described in the design are effective. Despite using real network communication, such systems can still be determinstically simulation-tested using tools like [Antithesis](https://antithesis.com/), which is currently picked up also by node-level tests in the Cardano community via [moog](https://github.com/cardano-foundation/moog). If we can put this technique to use for adversarial testing of Leios prototypes and release candidates, this can greatly enhance our ability to validate the protocol under challenging conditions by exploring a much wider range of adversarial scenarios than would be feasible through manually created rigit test scenarios.

Beyond networking prototypes, additional focused prototypes may be created to address other known unknowns of the implementation:

**Ledger validation benchmark:** measures the throughput of transaction validation and ledger state updates. This is critical for understanding whether a node can process the contents of large endorser blocks within the available time budget and confirm whether our models for transaction validation are correct. The benchmark explores different transaction types and sizes, measures the impact of caching strategies, and validates the performance improvement from the no-validation application of certified transactions.

**Cryptographic primitives prototype:** validates the performance and correctness of the BLS signature scheme integration. This includes key generation, signing, verification, and aggregation operations. The prototype must demonstrate that batch verification of large numbers of votes can complete within the voting period deadline. It also serves to validate the proof-of-possession mechanism and explore key rotation techniques.

Focused prototypes provide empirical data that complements the theoretical analysis. They reveal where optimizations are necessary and validate that the required performance is achievable with available hardware. They also serve to build developer confidence in the feasibility of the overall design, as well as directly validate and inform architectural decisions. Discovering a fundamental performance limitation early, through prototyping, is far preferable to discovering it late during testnet deployment or, worse, after mainnet deployment.

## Public testnets and integration

A public testnet serves distinct purposes over simulations and controlled environments: it requires integration of all components into a complete implementation, enables for tests under realistic conditions with diverse node operators and hardware, and allows the community to experience enhanced throughput directly. While some shortcuts can still be made, the testnet-ready implementation must offer complete Leios functionality - endorser block production and diffusion, vote aggregation, certificate formation, ledger integration, enhanced mempool - plus sufficient robustness for continuous operation and operational tooling for deployment and monitoring.

The testnet enables multiple validation categories. Functional testing verifies correct protocol operation: nodes produce endorser blocks when elected, votes aggregate into certificates, certified blocks incorporate into the ledger, and ledger state remains consistent. Performance testing measures achieved throughput against business requirements - sustained transaction rate, mempool-to-ledger latency, and behavior under bursty synthetic workloads. Adversarial testing is limited on a public testnet, but some attempts with deliberately misbehaving nodes can be made on withholding blocks, sending invalid data, attempting network partitioning, or resource exhaustion.

The testnet integrates ecosystem tooling: wallets handling increased throughput, block explorers understanding new structures, monitoring systems tracking Leios metrics, and stake pool operator documentation and deployment guides. Crucially, the testnet further enables empirical parameter selection (size limits, timing parameters), where simulation provides initial guidance but real-world testing with community feedback informs acceptable mainnet values.

Software deployed to the public testnet progressively converges toward mainnet release candidates. Early deployments may use instrumented prototypes lacking production optimizations; later upgrades run increasingly complete and optimized implementations. Eventually, all changes as [outlined in this design document](#technical-design) must be realized in the `cardano-node` and other node implementations. This progressive refinement maintains community engagement while preserving engineering velocity. Traces from testnet nodes can still be verified against formal specifications using the trace verification approach, ultimately linking the abstraction layers.

## Mainnet deployment readiness

Mainnet deployment requires governance approval and operational readiness beyond technical validation. The Cardano governance process involves delegated representatives and stake pool operators who need clear understanding of proposed changes, benefits, and risks. Technical validation evidence from formal methods, simulation, prototyping, and testnet operation must be communicated accessibly beyond technical documentation.

Operational readiness encompasses stake pool operator testing in their environments, updated procedures and training, clearly documented upgrade procedures, updated monitoring and alerting systems, and prepared support channels. The hard fork combinator enables relatively smooth transitions, but Leios represents substantial consensus changes. Conservative timeline estimates must account for discovering and addressing unexpected issues - a normal part of the hard-fork scheduling process. The months of validation and refinement required before prudent mainnet deployment reflect the critical nature of modifications to a system holding substantial economic value and providing essential services that users depend upon.

> [!WARNING]
>
> TODO: more thoughts:
>
> - why (deltaq) modeling? quick results and continued utility in parameterization
> - parameterization in general as a (communication) tool; see also Peras' parameterization dashboard https://github.com/tweag/cardano-peras/issues/54
> - what's left for the hard-fork after all this? more-and-more testing / maturing, governance-related topics (new protocol parameters, hard-fork coordination)

# Dependencies and interactions

The changes necessary to realizing Leios must integrate carefully with existing infrastructure and emerging features. This section examines the critical dependencies that must be satisfied before Leios deployment, identifies synergies with parallel developments, and analyzes potential conflicts that require careful coordination. The analysis informs both the implementation timeline and architectural decisions throughout the development process.

## On-disk storage of ledger state

> [!WARNING]
>
> TODO: Add some links and references to UTxO-HD and Ledger-HD specification and status

The transition from memory-based to disk-based ledger state storage represents a fundamental prerequisite for Leios deployment. This dependency stems directly from the throughput characteristics that Leios is designed to enable.

At the time of writing, the latest released `cardano-node` implementation supports UTxO state storage on disk through UTxO-HD, while other parts of the ledger state including reward accounts are put on disk within the Ledger-HD initiative. The completion of this transition is essential for Leios viability, as the increased transaction volume would otherwise quickly exhaust available memory resources on realistic hardware configurations.

The shift to disk-based storage fundamentally alters the resource profile of node operation. Memory requirements become more predictable and bounded, while disk I/O bandwidth and storage capacity emerge as primary constraints. Most significantly, ledger state access latency necessarily increases relative to memory-based operations, and this latency must be accounted for in the timing constraints that govern transaction validation.

Early validation through comprehensive benchmarking becomes crucial to identify required optimizations in ledger state access patterns. The (re-)validation of orders of magnitude bigger transaction closures, potentially initiated by multiple concurrent threads, places particular stress on the storage subsystem, as multiple validation threads may contend for access to the same underlying state. The timing requirements for vote production - where nodes must complete endorser block validation within the $L_\text{vote}$ period - on one hand, and applying (without validation) thousands transactions during block diffusion on the other hand, impose hard constraints on acceptable access latencies.

These performance characteristics must be validated empirically rather than estimated theoretically. The ledger prototyping described in the implementation plan must therefore include realistic disk-based storage configurations that mirror the expected deployment environment.

## Synergies with Peras

The relationship between Ouroboros Leios and Ouroboros Peras presents both opportunities for synergy and challenges requiring careful coordination. As characterized in the [Peras design](https://tweag.github.io/cardano-peras/peras-design.pdf) document, the two protocols are orthogonal in their fundamental mechanisms, Leios addressing throughput while Peras improves finality, but their concurrent development and potential deployment creates several interaction points.

**Resource contention and prioritization** emerges as the most immediate coordination challenge. Both protocols introduce additional network traffic that competes with existing Praos communication. The [resource management](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/ImpactAnalysis.md#resource-management) requirements for Leios - prioritizing Praos traffic above fresh Leios traffic above stale Leios traffic - must be extended to also accommodate Peras network messages. Any prioritization scheme requires careful analysis of the timing constraints for each protocol to ensure that neither compromises the other's security guarantees. Current understanding is that Peras traffic should be prioritized above both, stale and fresh Leios traffic, such that Leios protocol burst attacks may not force Peras into a cooldown period.

**Vote diffusion protocols** present a potential area for code reuse, though this opportunity comes with important caveats. The Leios implementation will initially evaluate the vote diffusion protocols [specified in CIP-164](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#leios-mini-protocols) for their resilience against protocol burst attacks and general performance characteristics. Once the Peras [object diffusion mini-protocol](https://tweag.github.io/cardano-peras/peras-design.pdf#section.2.5) becomes available, it should also be evaluated for applicability to Leios vote diffusion. However, the distinct performance requirements and timing constraints of the two protocols may ultimately demand separate implementations despite structural similarities.

**Cryptographic infrastructure** offers the most promising near-term synergy. Both protocols are based on signature schemes using BLS12-381 keys, creating an opportunity for shared cryptographic infrastructure. If key material can be shared across protocols, stake pool operators would need to generate and register only one additional key pair rather than separate keys for each protocol. This shared approach would significantly simplify the bootstrapping process for whichever protocol deploys second.

The [Peras requirement](https://tweag.github.io/cardano-peras/peras-design.pdf#appendix.B) for forward secrecy may necessitate the use of [Pixel signatures](https://eprint.iacr.org/2019/514.pdf) on top of the BLS12-381 curve, in addition to BLS (as a VRF) for committee membership proofs, but this is completely independent of Leios requirements. Furthermore, the proof-of-possession mechanisms required for BLS aggregation are identical across both protocols, allowing for shared implementation and validation procedures.

**Protocol-level interactions** between Leios certified endorser blocks and Peras boosted blocks represent a longer-term research opportunity. In principle, the vote aggregation mechanisms used for endorser block certification could potentially be leveraged for Peras boosting, creating a unified voting infrastructure. However, such integration is likely undesirable for initial deployments due to the complexity it would introduce and the dependency it would create between the two protocols. In the medium to long term, exploring these interactions could yield further improvements to both throughput and finality properties.

## Era and hard-fork coordination

As already identified in the [impact analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/ImpactAnalysis.md#ledger), Leios requires a new ledger era to accommodate the modified block structure and validation rules. The timing of this transition must be carefully coordinated with the broader Cardano hard-fork schedule and other planned protocol upgrades.

At the time of writing, the currently deployed era is `Conway`, with `Dijkstra` planned as the immediate successor. Current plans for `Dijkstra` include nested transactions and potentially Peras integration. Before that, an intra-era hard fork is planned for early 2026 to enable additional features within the `Conway` era still.

A new era is always required when the allowed encoding of block bodies and transactions change. As `Dijkstra` is the current "staging era", it will also be the integration point for Leios-specific format changes. Should development timelines turn out not to align with the inter-era hard-fork schedule to `Dijkstra`, there are two options:

- Postpone Leios deployment until after `Dijkstra`, moving Leios block format changes into the subsequent era `Euler`.
- Leios block format encoding specification and implementation remains in `Dijkstra`, but ledger validation is always failing until an intra-era hard-fork enables it.

While the first option appears "cleaner", it could introduce substantial delays depending on the community-agreed pace on new era definition and deployments. The second option on the other hand requires definite understanding on the serialization format ahead of time, where any further change would result in option one of targeting `Euler`, but with the added friction of feature-flagging Leios functionality before its moved to `Euler` - the worst of both options.

Deploying both Peras and Leios within the same hard fork is technically possible but increases deployment risk. Both protocols represent significant consensus changes that affect network communication patterns, resource utilization, and operational procedures. The complexity of coordinating these changes, validating their interactions, and managing the upgrade process across the diverse Cardano ecosystem suggests that sequential deployment provides a more conservative and manageable approach. Both options above would allow for that via two subsequent protocol versions, but also both in one hard-fork if the risk is deemed acceptable.

## Interactions with Genesis

Ouroboros Genesis enables nodes to bootstrap safely from the genesis block with minimal trust assumptions, completing the decentralization of Cardano's physical network infrastructure. Genesis integration with Leios requires **no** changes to the existing Genesis State Machine, though practical considerations on synchronization remain important.

**Genesis compatibility** directly follows from the protocol design. The Genesis protocol operates on ranking block headers for chain density calculations and bootstrapping decisions. Since Leios preserves the existing ranking block sequence while only adding certificates of endorser blocks, the fundamental Genesis mechanisms remain unchanged. No modifications to the Genesis State Machine are expected, as it continues to evaluate the unchanged chain growth.

**Chain synchronization** in general becomes more complex under Leios due to the multi-layered block structure. Syncing nodes must fetch both ranking blocks and their associated certified endorser blocks to construct a complete view of the chain. A node that downloads only ranking blocks cannot reconstruct the complete ledger state, as the actual transactions content resides within closures of the endorser blocks referenced by certificates on the ranking blocks. The `LeiosFetch` mini-protocol addresses this requirement through the `MsgLeiosBlockRangeRequest` message type, enabling efficient batch fetching of complete block ranges during synchronization. This allows nodes to request not only a range of ranking blocks but also all associated endorser blocks and their transaction closures in coordinated requests. Parallel fetching from multiple peers becomes critical for synchronization performance, as the data volume substantially exceeds that of traditional Praos blocks.

> ![WARNING]
>
> TODO: Chain synchronization / syncing node discussion could be moved to the respective section in the architecture/changes chapter

## Impact on Mithril

While Mithril operates as a separate layer above the consensus protocol and does not directly interact with Leios mechanisms, the integration requires consideration of several practical compatibility aspects.

The most prominent feature of Mithril is that it serves verifable snapshots of the `cardano-node` databases. The additional data structures introduced by Leios (e.g. the EBStore) must be incorporated into the snapshots that Mithril produces and delivers to its users. Beyond that, Mithril needs to also extend its procedures for digesting and verifying the more complex chain structure including endorser blocks and their certification status.

Mithril relies on a consistent view of the blockchain across all participating signers. Hence, the client APIs used by Mithril signers may require updates depending on which interfaces are utilized. While Mithril initially focused on digesting and signing the immutable database as persisted on disk, the consideration of using `LocalChainSync` for signing block ranges introduces potential interaction points with Leios induced [changes to client interface](#client-interfaces).

In summary, Leios will not require fundamental changes to Mithril's architecture but requires careful attention to data completeness and consistency checks in the snapshot generation and verification processes.

# Risks and mitigations

> [!WARNING]
>
> TODO: Introduce chapter as being the bridge between implementation plan and concrete technical design; also, these are only selected aspects that inform the implementation (and not cover principal risks to the protocol or things that are avoided by design)

## Key threats

> [!WARNING]
>
> TODO: Selection of key threats and attacks that further inform the design and/or implementation plan. Incorporate / reference the full [threat model](../threat-model.md)

### Protocol bursts

> [!WARNING]
>
> TODO: important because
>
> - was a prominent case in research
> - acknowledges the wealth of data to be processed
> - mitigation: freshest-first delivery / prioritization between praos and leios traffic
> - motivates experiments/features revolving around resource management
> - reference/include/move related RSK-.. items from impact analysis

### Data withholding

> [!WARNING]
>
> TODO: important because
>
> - can be done from stake- and network-based attackers
> - trivially impacts high-throughput because no certifications happening
> - however, more advanced, potential avenue to attack blockchain safety (impact praos security argument) when carefully partitioning the network
> - mitigation: L_diff following the [security argument](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#protocol-security)
> - motivates validation of optimistic and worst-case diffusion paths

## Assumptions to validate early

> [!WARNING]
>
> TODO: Which assumptions in the CIP / on the protocol security need to be validated as early as possible?
>
> - Worst case diffusion of EBs given certain honest stake (certifying the EB) is realistic
> - The cardano network stack can realize freshest first delivery (sufficiently well)
> - A real ledger can (re-)process orders of magnitude higher loads as expected
> - ...?

# Technical design

> [!CAUTION]
>
> FIXME: The next few sections are basically the relevant parts of the impact analysis and ought to expanded with anything concrete implementation designs.
>
> When transferring things from impact analysis, the **REQ-...** requirements are as well as the **NEW-..** and **UPD-..** references were kept. Not sure if we need all of them to references between concepts and designs.

> [!WARNING]
>
> TODO: How to structure the changes best? Group them by layer/component or responsibility?
>
> Behavior-based sketch:
> - Transaction submission and caching
> - EB production
> - EB diffusion
> - EB storage
> - Voting committee selection
>   - Key generation
>   - Key registration
>   - Key rotation
> - Vote production
> - Vote diffusion
> - Certification
>   - Block production: Including certificates in blocks
>   - Chain validation: Verifying certificates in blocks
>   - Staging area interactions?
>
> See also this mind map of changes as created by @nfrisby:
>
> ``` mermaid
> mindmap
>   root((Leios tasks, core devs))
>     ((Ledger))
>       Serialization
>         Certs in RB bodies<br>- akin to Peras
>         Cert codecs/CDDL
>       New protocol parameters
>       New pool voting keys<br>- akin to Peras
>       Cert validation
>       New LocalStateQuery queries?
>       Tune EB limits
>     ((Consensus---easier))
>       Serialization
>         New fields in RB header
>         EB codecs/CDDL
>         Vote codecs/CDDL
>       Storage
>         EBs - imm and vol
>         Txs of EBs - imm and vol
>         Votes - only vol
>         Tx cache
>       Vote validation
>       Mempool
>          Increase size
>          Slurp from EBs
>       New Tracer events
>       New LocalStateQuery queries?
>       Add included EBs to NodeToClient ChainSync
>     ((Consensus---harder))
>       Prioritize Praos threads
>       Vote decision logic
>       Genesis State Machine transition predicates
>     ((Network))
>       Prioritize Praos traffic
>       Prioritize Praos threads
>     ((Network&Consensus))
>       New mini protocols
>         Message codecs/CDDL
>         Tune size and time limits
>         Tune pipelining depth
>       Fetch decision logic
>         Caught up
>         Bulk syncing
>       Freshest first delivery
>         either: conservative pipelining depths
>         and/or else: server-side reordering
>     ((Node))
>       New config data    
>       Feature flags for dev phases
>       New CLI queries?
>       New pool voting keys<br>- akin to Peras
> ```

## Architecture

While being a significant change to the consensus protocol, Leios does not require fundamental changes to the overall architecture of the `cardano-node`. Several new components will be needed for the new responsibilities related to producing and relaying Endorser Blocks (EBs) and voting on them, as well as changes to existing components to support higher throughput and freshest-first-delivery. The following diagram illustrates the key components of a relay node where new and updated components are marked in purple:

> [!WARNING]
>
> TODO: Should consider adding Leios prefixes to VoteStore (to not confuse with PerasVoteDB), i.e. LeiosVoteDB?

![](./relay-leios-component-diagram.svg)

> [!WARNING]
>
> TODO: Explain why focus on relay node (upstream/downstream relationship); briefly mention block producer node differences; Add similar diagram for block producer? block and vote production not shown in relay diagram

## Consensus

> [!WARNING]
>
> TODO: Mostly content directly taken from [impact analysis](../ImpactAnalysis.md). Expand on motivation and concreteness of changes.

CIP-0164 implies functional requirements for the node to issue EBs alongside RBs, vote for EBs according to the rules from the CIP, include certificates when enough votes are seen, diffuse EBs and votes through the network layer, and retain EB closures indefinitely when certified. The Consensus layer is responsible for driving these operations and coordinating with the Network layer (which implements the actual mini-protocols) to ensure proper diffusion.

### Block production

The existing block production thread must be updated to generate an EB at the same time it generates an RB (**UPD-LeiosAwareBlockProductionThread**). In particular, the hash of the EB is a field in the RB header, and so the RB header can only be decided after the EB is decided, and that can only be after the RB payload is decided. Moreover, the RB payload is either a certificate or transactions, and that must also be decided by this thread, making it intertwined enough to justify doing it in a single thread.

- **REQ-IssueLeiosBlocks** The node must issue an EB alongside each RB it issues, unless that EB would be empty.
- **REQ-IncludeLeiosCertificates** The node must include a certificate in each RB it issues if it has seen enough votes supporting the EB announced by the preceding RB. (TODO excluding empty or very nearly empty EBs?)

The Mempool capacity should be increased (**UPD-LeiosBiggerMempool**) to hold enough valid transactions for the block producer to issue a full EB alongside a full RB. The Mempool capacity should at least be twice the capacity of an EB, so that the stake pool issuing a CertRB for a full EB would still be able to issue a full EB alongside that CertRB (TxRB's have less transaction capacity than the EB certified by a CertRB). In general, SPOs are indirectly incentivized to maximize the size of the EB, just like TxRBs—so that more fees are included in the epoch's reward calculation.

### Vote production and storage

A new thread dedicated to Leios vote production (**NEW-LeiosVoteProductionThread**) will wake up when the closure of an EB is newly available. If the voting rules would require the stake pool to vote (now or soon) for this EB if it's valid, then this thread will begin validating it. Note if multiple closures arrive simultaneously, at most one of them could be eligible for a vote, since the voting rules require the EB to be announced by the tip of the node's current selection. If the validation succeeds while the voting rules still require the stake pool to vote for this EB (TODO even if it has since switched its selection?), the thread will issue that vote.

- **REQ-IssueLeiosVotes** The node must vote for EBs exactly according to the rules from the CIP.

A new storage component (**NEW-LeiosVoteStorage**) will store all votes received by a node, up to some conservative age (eg ten minutes). As votes arrive, they will be grouped according to the RB they support. When enough votes have arrived for some RB, the certificate can be generated immediately, which can avoid delaying the potential subsequent issuance of a CertRB by this node. A vote for the EB announced by an RB is irrelevant once all nodes will never switch their selection away from some block that is not older than that RB. This condition is very likely to be satisfied relatively soon on Cardano mainnet, unless its Praos growth is being disrupted. Therefore, the vote storage component can simply discard votes above some conservative age, which determines a stochastic upper bound the heap size of all sufficiently-young votes.

- **REQ-DiffuseLeiosVotes** The node must diffuse votes (via the Network layer's mini-protocols) at least until they're old enough that there remains only a negligible probability they could still enable an RB that was issued on-time to include a certificate for the EB they support.

### Endorser block storage

Unlike votes, a node should retain the closures of older EBs (**NEW-LeiosEbStore**), because Praos allows for occasional deep forks, the most extreme of which could require the closure of an EB that was announced by the youngest block in the Praos Common Prefix. On Cardano mainnet, that RB is usually 12 hours old, but could be up to 36 hours old before [CIP-0135 Disaster Recovery Plan](https://cips.cardano.org/cip/CIP-0135) is triggered. Thus, EB closures are not only large but also have a prohibitively long lifetime even when they're ultimately not immortalized by the historical chain. This component therefore stores EBs on disk just as the ChainDB already does for RBs. The volatile and immutable dichotomy can even be managed the same way it is for RBs.

- **REQ-DiffuseLeiosBlocks** The node must acquire and diffuse EBs and their closures (via the Network layer's new mini-protocols, see below).
- **REQ-ArchiveLeiosBlocks** The node must retain each EB's closure indefinitely when the settled Praos chain certifies it.

Each CertRB must be buffered in a staging area (**NEW-LeiosCertRbStagingArea**) until its closure arrives, since the VolDB only contains RBs that are ready for ChainSel. (Note that a CertRB's closure will usually have arrived before it did.) (TODO Any disadvantages? For example, would it be beneficial to detect an invalid certificate before the closure arrives?) (TODO a more surgical alternative: the VolDB index could be aware of which EB closures have arrived, and the path-finding algorithm could incorporate that information. However, this means each EB arrival may need to re-trigger ChainSel.) The BlockFetch client (**UPD-LeiosRbBlockFetchClient**) must only directly insert a CertRB into the VolDB if its closure has already arrived (which should be common due to L_diff). Otherwise, the CertRB must be deposited in the CertRB staging area instead.

The LedgerDB (**UPD-LeiosLedgerDb**) will need to retrieve the certified EB's closure from the LeiosEbStore when applying a CertRB. Due to NEW-LeiosCertRbStagingArea, it should be impossible for that retrieval to fail.

### Transaction cache

A new storage component (**NEW-LeiosTxCache**) will store all transactions received when diffusing EBs as well as all transactions that successfully enter the Mempool, up to some conservative age (eg one hour). The fundamental reason that EBs refer to transactions by hash instead of including them directly is that, for honest EBs, the node will likely have already received most of the referenced transactions when they recently diffused amongst the Mempools. That's not guaranteed, though, so the node must be able to fetch whichever transactions are missing, but in the absence of an attack that ought to be minimal.

The Mempool is the natural inspiration for this optimization, but it's inappropriate as the actual cache for two reasons: it has a relatively small, multidimensional capacity and its eviction policy is determined by the distinct needs of block production. This new component instead has a greater, unidimensional capacity and a simple Least Recently Used eviction policy. Simple index maintained as a pair of priority queues (index and age) in manually managed fixed size bytearrays, backed by a double-buffered mmapped file for the transactions' serializations. Those implementation choices prevent the sheer number of transactions from increasing GC pressure (adversarial load might lead to a ballpark number of 131000 transactions per hour), and persistence's only benefit here would be to slightly increase parallelism/simplify synchronization, since persistence would let readers release the lock before finishing their search.

Note: if all possibly-relevant EBs needed to fit in the LeiosTxCache, its worst case size would approach 500 million transactions. Even the index would be tens of gigabytes. This is excessive, since almost all honest traffic will be younger than an hour—assuming FFD is actually enforced.

### Resource management

The protocol requires resource-management to prioritize Praos traffic and computation over all Leios traffic, and prioritize younger EBs over older ones:

- **REQ-PrioritizePraosOverLeios** The node must prioritize Praos traffic and computation over all Leios traffic and computation so that the diffusion and adoption of any RB is only negligibly slower.
- **REQ-PrioritizeFreshOverStaleLeios** The node must prioritize Leios traffic and computation for younger EBs over older EBs (a.k.a. freshest first delivery).

These requirements can be summarized as: Praos > fresh Leios > stale Leios. The Consensus layer implements the scheduling logic to satisfy these requirements, while the Network layer (see below) implements the protocol mechanisms. Looking forward, Peras should also be prioritized over Leios, since a single Peras failure is more disruptive to Praos than a single Leios failure.

The fundamental idea behind Leios has always been that the Praos protocol is inherently and necessarily bursty. Leios should be able to freely utilize the nodes' resources whenever Praos is not utilizing them, which directly motivates **REQ-PrioritizePraosOverLeios**. It is ultimately impossible to achieve such time-multiplexing perfectly, due to the various latencies and hystereses inherent to the commodity infrastructure (non real-time operating systems, public Internet, etc). On the other hand, it is also ultimately unnecessary to time-multiplex Praos and Leios perfectly, but which degree of imperfection is tolerable?

> [!WARNING]
>
> TODO: Move description of protocol burst attack vector into dedicated section (above)

One particularly relevant attack vector is the protocol burst attack (**ATK-LeiosProtocolBurst**). In a protocol burst attack the adversary withholds a large number of EBs and/or their closures over a significant duration and then releases them all at once. This will lead to a sustained maximal load on the honest network for a smaller but still significant duration, a.k.a. a burst. The potential magnitude of that burst will depend on various factors, including at least the adversary's portion of stake, but the worst-case is more than a gigabyte of download. The cost to the victim is merely the work to acquire the closures and to check the hashes of the received EB bodies and transaction bodies. In particular, at most one of the EBs in the burst could extend the tip of a victim node's current selection, and so that's the only EB the victim would attempt to fully parse and validate.

Contention for the following primary node resources might unacceptably degrade the time-multiplexing via contention between Praos and Leios:

- **RSK-LeiosPraosContentionNetworkBandwidth** This is not anticipated to be a challenge, because time-multiplexing the bandwidth is relatively easy. In fact, Leios traffic while Praos is idle could potentially even prevent the TCP Receive Window from contracting, thus avoiding a slow start when Praos traffic resumes.
- **RSK-LeiosPraosContentionCPU** This is not anticipated to be a challenge, because today's Praos node does not exhibit major CPU load on multi-core machines. Leios might have more power-to-weight ratio for parallelizing its most expensive task (EB validation), but that parallelization isn't yet obviously necessary. Thus, even Praos and Leios together do not obviously require careful orchestration on a machine with several cores.
- **RSK-LeiosPraosContentionGC** It is not obvious how to separate Praos and Leios into separate OS processes, since the ledger state is expensive to maintain and both protocols frequently read and update it. When the Praos and Leios components both run within the same operating system process, they share a single instance of the GHC Runtime System (RTS), including eg thread scheduling and heap allocation. The sharing of the heap in particular could result in contention, especially during an ATK-LeiosProtocolBurst (at least the transaction cache will be doing tens of thousands of allocations, in the worst-case). Even if the thread scheduler could perfectly avoid delaying Praos threads, Leios work could still disrupt Praos work, because some RTS components exhibit hysteresis, including the heap.
- **RSK-LeiosPraosContentionDiskBandwidth** Praos and Leios components might contend for disk bandwidth. In particular, during a worst-case ATK-LeiosProtocolBurst, the Leios components would be writing more than a gigabyte to disk as quickly as the network is able to acquire the bytes (from multiple peers in parallel). Praos's disk bandwidth utilization depends on the leader schedule, fork depth, etc, as well as whether the node is using a non-memory backend for ledger storage (aka UTxO HD or Ledger HD). For non-memory backends, the ledger's disk bandwidth varies drastically depending on the details of the transactions being validated and/or applied: a few bytes of transaction could require thousands of bytes of disk reads/writes.
  - Note that the fundamental goals of Leios will imply a significant increase in the size of the UTxO. In response, SPOs might prefer enabling UTxO HD/Ledger HD over buying more RAM.

Both GC pressure and disk bandwidth are notoriously difficult to model and so were not amenable to the simulations that drove the first version of the CIP. Prototypes rather than simulations will be necessary to assess these risks with high confidence.

The same risks can also be viewed from a different perspective, which is more actionable in terms of planning prototypes/experiments/etc: per major component of the node.

- **RSK-LeiosLedgerOverheadLatency**: Parsing a transaction, checking it for validity, and updating the ledger state accordingly all utilize CPU and heap (and also disk bandwidth with UTxO/Ledger HD). Frequent bursts of that resource consumption proportional to 15000% of a full Praos block might disrupt the caught-up node in heretofore unnoticed ways. Only syncing nodes have processed so many/much transactions in a short duration, and latency has never been a fundamental priority for a syncing node. Disruption of the RTS is the main concern here, since there is plenty of CPU available—the ledger is not internally parallelized, and only ChainSel and the Mempool could invoke it simultaneously.
- **RSK-LeiosNetworkingOverheadLatency**: Same as RSK-LeiosLedgerOverheadLatency, but for the Diffusion Layer components handling frequent 15000% bursts in a caught-up node.
- **RSK-LeiosMempoolOverheadLatency**: Same as RSK-LeiosLedgerOverheadLatency, but for the Mempool frequently revalidating 15000% load in a caught-up node during congestion (ie 30000% the capacity of a Praos block, since the Leios Mempool capacity is now two EBs instead of two Praos blocks).

### Implementation notes

For the first version of the LedgerDB, it need not explicitly store EB's ledger state; the CertRB's result ledger state will reflect the EB's contents. A second version could thunk the EB's reapplication alongside the announcing RB, which would only avoid reapplication of one EB on a chain switch (might be worth it for supporting tiebreakers?). The first version of LedgerDB can simply reapply the EB's transactions before tick-then-applying a CertRB. A second version should pass the EB's transactions to the ledger function (or instead the thunk of reapplying the EB)?

The first version of the Mempool can be naive, with the block production thread handling everything. A second version can try to pre-compute in order to avoid delays (ie discarding the certified EB's chunk of transactions) when issuing a CertRB and its announced EB.

The first version of LeiosTxCache should reliably cache all relevant transactions that are less than an hour or so old—that age spans 180 active slots on average. A transaction is born when its oldest containing EB was announced or when it _entered_ the Mempool (if it hasn't yet been observed in an EB). (Note that that means some tx's age in the LeiosTxCache can increase when an older EB that contains it arrives.) Simple index maintained as a pair of priority queues (index and age) in manually managed fixed size bytearrays, backed by a double-buffered mmapped file for the transactions' serializations. Those implementation choices prevent the sheer number of transactions from increasing GC pressure (adversarial load might lead to a ballpark number of 131000 transactions per hour), and persistence's only benefit here would be to slightly increase parallelism/simplify synchronization, since persistence would let readers release the lock before finishing their search.

The first version of LeiosFetch client can assemble the EB closure entirely on disk, one transaction at a time. A second version might want to batch the writes in a pinned mutable `ByteArray` and use `withMutableByteArrayContents` and `hPutBuf` to flush each batch. Again, the possible benefit of this low-level shape would be to avoid useless GC pressure. The first version can wait for all transactions before starting to validate any. A later version could eagerly validate as the prefix arrives—comparable to eliminating one hop in the topology, in the worst-case scenario.

The first version of LeiosFetch server simply pulls serialized transactions from the LeiosEbStore, and only sends notifications to peers that are already expecting them when the noteworthy event happens. If notification requests and responses are decoupled in a separate mini protocol _or else_ requests can be reordered (TODO or every other request supports a "MsgOutOfOrderNotificationX" loopback alternative?), then it'll be trivial for the client to always maintain a significant buffer of outstanding notification requests.

Even the first version of LeiosFetch decision logic should consider EBs that are certified on peers' ChainSync candidates as available for request, as if that peer had sent both MsgLeiosBlockOffer and MsgLeiosBlockTxsOffer. A MsgRollForward implies the peer has selected the block, and the peer couldn't do that for a CertRB if it didn't already have its closure.

The first version of LeiosEbStore can just be two bog standard key-value stores, one for immutable and one for volatile. A second version maybe instead integrates certified EBs into the existing ImmDB? That integration seems like a good fit. It has other benefits (eg saves a disk roundtrip and exhibits linear disk reads for driver prefetching/etc), but those seem unimportant so far.

## Network

> [!WARNING]
>
> TODO: Mostly content directly taken from [impact analysis](../ImpactAnalysis.md). Expand on motivation and concreteness of changes.

The Network layer implements the mini-protocols that enable the Consensus layer to satisfy its diffusion requirements (**REQ-DiffuseLeiosBlocks**, **REQ-DiffuseLeiosVotes**) and prioritization requirements (**REQ-PrioritizePraosOverLeios**, **REQ-PrioritizeFreshOverStaleLeios**) defined in the Consensus section above. While Consensus drives the scheduling logic for when to diffuse blocks and votes, Network provides the protocol mechanisms to actually transmit them over the peer-to-peer network.

Similar resource contention risks apply to the Network layer, including network bandwidth contention between Praos and Leios, networking overhead latency, and contention between fresh and stale Leios traffic.

### New mini-protocols

The node must include new mini-protocols (**NEW-LeiosMiniProtocols**) to diffuse EB announcements, EBs themselves, EBs' transactions, and votes for EBs. These protocols enable the Consensus layer to satisfy **REQ-DiffuseLeiosBlocks** and **REQ-DiffuseLeiosVotes**. The Leios mini-protocols will require new fetch decision logic (**NEW-LeiosFetchDecisionLogic**), since the node should not necessarily simply download every such object from every peer that offers it. Such fetch decision logic is also required for TxSubmission and for Peras votes; the Leios logic will likely be similar but not equivalent.

### Traffic prioritization

The existing multiplexer is intentionally fair amongst the different mini-protocols. In the current CIP, the Praos traffic and Leios traffic are carried by different mini-protocols. Therefore, introducing a simple bias in the multiplexer (**NEW-LeiosPraosMuxBias**) to strongly (TODO fully?) prefer sending messages from Praos mini protocols over messages from Leios mini protocols would directly enable the Consensus layer to satisfy **REQ-PrioritizePraosOverLeios** and mitigate **RSK-LeiosPraosContentionNetworkBandwidth**. This multiplexer bias is the primary mechanism to ensure that Praos traffic and computation are prioritized over Leios, so that the diffusion and adoption of any RB is only negligibly slower.

It is not yet clear how best to mitigate **RSK-LeiosLeiosContentionNetworkBandwidth** or, more generally, how to enable the Consensus layer to satisfy **REQ-PrioritizeFreshOverStaleLeios** (aka freshest first delivery) in the Network Layer. One notable option is to "rotate" the two proposed Leios mini-protocols into a less natural pair: one would send all requests and only requests and the other would send all replies and only replies. In that way, the server can—when it has received multiple outstanding requests, which seems likelying during ATK-LeiosProtocolBurst—reply to requests in a different order than the client sent them, which is inevitable since the client will commonly request an EB as soon it's offered, which means the client will request maximally fresh EBs after having requesting less fresh EBs. If the client were to avoid sending any request that requires a massive atomic reply (eg a MsgLeiosBlockTxsRequest for 10 megabytes), then the server can prioritize effectively even without needing to implement any kind of preemption mechanism. This option can be formulated in the existing mini protocol infrastructure, but another option would be to instead enrich the mini-protocol infrastructure to somehow directly allow for server-side reordering. Whether any of this is needed requires further investigation through prototypes (EXP-LeiosDiffusionOnly).


## Ledger

> [!WARNING]
>
> TODO: Mostly content directly taken from [impact analysis](../ImpactAnalysis.md). Expand on motivation and concreteness of changes.

The [Ledger](https://cardano-scaling.github.io/cardano-blueprint/ledger/index.html) is responsible for validating Blocks and represents the actual semantics of Cardano transactions. CIP-164 sketches a protocol design that does not change the semantics of Cardano transactions, does not propose any changes to the transaction structure and also not requires changes to reward calculation. The ledger component has three main entry points:

1. Validating individual transactions via [`LEDGER`](https://intersectmbo.github.io/formal-ledger-specifications/site/Ledger.Conway.Specification.Ledger.html#ledger-transition-system)
2. Validating entire block bodies via [`BBODY`](https://intersectmbo.github.io/formal-ledger-specifications/site/Ledger.Conway.Specification.BlockBody.html#block-body-transition)
3. Updating rewards and other ledger state (primarily across epochs) via [`TICK`](https://intersectmbo.github.io/formal-ledger-specifications/site/Ledger.Conway.Specification.RewardUpdate.html#chain-tick-transition)

The first will not need to change functionally, while the latter two will need to be updated to handle the new block structure (ranking blocks not including transactions directly) and to enable the determination of a voting committee for certificate verification. Any change to the ledger demands a hard-fork and a change in formats or functionality are collected into [ledger eras](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0084#ledger-eras). The changes proposed by CIP-164 will need to go into new ledger era:

- **REQ-LedgerNewEra** The ledger must be prepared with a new era that includes all changes required by CIP-164.

For the remainder of this document, let's assume the changes will go into the `Euler` era, where `Conway` is currently the latest and `Dijkstra` is in preparation at the time of writing.

### Transaction validation levels

Validating individual transactions is currently done either via `applyTx` or `reapplyTx` functions. This corresponds to two levels of validation:

- `applyTx` fully validates a transaction, including existence of inputs, checking balances, cryptographic hashes, signatures, evaluation of plutus scripts, etc.
- `reapplyTx` only check whether a transaction applies to a ledger state. This does not include expensive checks like script evaluation (a.k.a phase-2 validation) or signature verification.

Where possible, `reapplyTx` is used when we know that the transaction has been fully validated before. For example when refreshing the mempool after adopting a new block. With Leios, a third level of validation is introduced:

- **REQ-LedgerTxNoValidation** The ledger should provide a way to update the ledger state by just applying a transaction without validation.

This third way of updating a ledger state would be used when we have a valid certificate about endorsed transactions in a ranking block. To avoid delaying diffusion of ranking blocks, we do want to do the minimal work necessary once an EB is certified and ease the [protocol security argument](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#protocol-security) with:

- **REQ-LedgerCheapReapply** Updating the ledger state without validation must be significantly cheaper than even reapplying a transaction is today.

Note that this already anticipates that the new, third level `notValidateTx` will be even cheaper than `reapplyTx`. [Existing benchmarks](https://github.com/IntersectMBO/cardano-ledger/tree/master/libs/ledger-state) indicate that `reapplyTx` is already at least one order of magnitude cheaper than `applyTx` for transactions.

### New block structure

In Praos, all transactions to be verified and applied to the ledger state are included directly in the block body. In Leios, ranking blocks (RB) may not include transactions directly, but instead certificate and reference to an endorsement block (EB) that further references the actual transactions. This gives rise to the following requirements:

- **REQ-LedgerResolvedBlockValidation** When validating a ranking block body, the ledger must be provided with all endorsed transactions resolved.
- **REQ-LedgerUntickedEBValidation** When validating a ranking block body, the ledger must validate endorsed transactions against the ledger state before updating it with the new ranking block.
- **REQ-LedgerTxValidationUnchanged** The actual transaction validation logic should remain unchanged, i.e., the ledger must validate each transaction as it does today.

The endorsement block itself does not contain any additional information besides a list of transaction identifiers (hashes of the full transaction bytes). Hence, the list of transactions is sufficient to reconstruct the EB body and verify the certificate contained in the RB. The actual transactions to be applied to the ledger state must be provided by the caller of the ledger interface, typically the storage layer.

### Certificate verification

In order to verify certificates contained in ranking blocks, the ledger must be aware of the voting committee and able to access their public keys. As defined by **REQ-RegisterBLSKeys**, SPOs must be able to register their BLS keys to become part of the voting committee. The ledger will need to be able to keep track of the registered keys and use them to do certificate verification. Besides verifying certificates, individual votes must also be verifiable by other components (e.g. to avoid diffusing invalid votes).

- **REQ-LedgerStateVotingCommittee** The Leios voting committee must be part of the ledger state, updated on epoch boundaries and queryable through existing interfaces.

Being part of the ledger state, the voting committee will be stored in ledger snapshots and hence on disk in course of Ledger-HD. Depending on how exactly keys will be registered, the ledger might need to be able to access block headers in order to read the BLS public keys from the operational certificate. As this is not the case today (only block bodies are processed by the ledger), this results in requirement:

- **REQ-LedgerBlockHeaderAccess** The ledger must be able to access block headers.

> [!NOTE]
> This is a very generic requirement and will likely change depending on how the consensus/ledger interface for block validation is realized. It might be desirable to limit the ledger's access to block headers and only provide (a means to extract) relevant information. That is, the BLS public keys to be tracked and the voting committee to be selected from.

The voting committee consists of persistent and non-persistent voters. The persistent voters are to be selected at epoch boundaries using a [Fait Accompli sortition scheme](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#votes-and-certificates). Hence:

- **REQ-LedgerCommitteeSelection** The ledger must select persistent voters in the voting committee at epoch boundaries using the Fait Accompli sortition scheme.

Finally, block validation of the ledger can use the voting committee state to verify certificates contained in ranking blocks:

- **REQ-LedgerCertificateVerification** The ledger must verify certificates contained in ranking blocks using the voting committee state.

### New protocol parameters

CIP-164 introduces several new protocol parameters that may be updated via on-chain governance. The ledger component is responsible for storing, providing access and updating any protocol parameters. Unless some of the new parameters will be deemed constant (a.k.a globals to the ledger), the following requirements must be satisfied for all new parameters:

- **REQ-LedgerProtocolParameterAccess** The ledger must provide access to all new protocol parameters via existing interfaces.
- **REQ-LedgerProtocolParameterUpdate** The ledger must be able to update all new protocol parameters via on-chain governance.

Concretely, this means defining the `PParams` and `PParamsUpdate` types for the `Euler` era to include the new parameters, as well as providing access via the `EulerPParams` and other type classes.

### Serialization

Traditionally, the ledger component defines the serialization format of blocks and transactions. CIP-164 introduces three new types that need to be serialized and deserialized:

> [!WARNING]
>
> TODO: Serialization of votes a consensus component responsibility?

- **REQ-LedgerSerializationRB** The ranking block body contents must be deterministically de-/serializable from/to bytes using CBOR encoding.
- **REQ-LedgerSerializationEB** The endorsement block structure must be deterministically de-/serializable from/to bytes using CBOR encoding.
- **REQ-LedgerSerializationVote** The vote structure must be deterministically de-/serializable from/to bytes using CBOR encoding.

Corresponding types with instances of `EncCBOR` and `DecCBOR` must be provided in the ledger component. The `cardano-ledger` package is a dependency to most of the Haskell codebase, hence these new types can be used in most other components.

## Cryptography

> [!WARNING]
>
> Work in progress. Content is created based on [impact analysis](../ImpactAnalysis.md), [Leios crypto project board](https://github.com/orgs/IntersectMBO/projects/75), and [CIP](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md).


In Leios, EBs are compactly certified for inclusion in RBs. 
Certification is achieved through a voting mechanism in which committee members cast votes referencing specific EBs, and these votes are then aggregated into compact certificates. 

To participate in the Leios protocol as a voting member or block-producing node, stake pool operators must register an additional cryptographic key dedicated to the voting scheme, alongside their existing VRF and KES keys.
Two types of voters contribute to EB validation, ensuring a balance between security, decentralization, and efficiency. 
Persistent voters are selected once per epoch and participate in every election, identified by compact identifiers. 
Non-persistent voters, on the other hand, are selected independently for each EB via local sortition. 
Registered voters can generate and cast votes, each including an `endorser_block_hash` field that uniquely identifies the target EB. 
Collected votes are then aggregated into a compact certificate.

### Leios Voting in a Nutshell

#### Key Generation
- A secret key ($sk$) is created to generate signatures for the corresponding signature scheme.  
- The public key ($pk$) is securely derived from $sk$ and used to verify the corresponding signatures.  
- A proof of possession ($PoP$) is generated for $sk$ to ensure key ownership.  
> Note that keys are not rotated periodically, as forward security is not required for IBs, EBs, or votes.

#### Key Registration 
- The registration process is responsible for storing public keys and verifying proof of possession.  
- Each stake pool registers with the following information:  
  - A unique identifier (Pool ID or similar)  
  - $pk$  
  - $PoP$  
  - A KES signature over the Pool ID, $pk$, and $PoP$  
- Nodes verify the $PoP$s of all received $pk$s to confirm their validity.

#### Voter Determination
- For each epoch, *persistent voters* are selected based on the stake distribution and participate in every election during that epoch.  
- Within the same epoch, *non-persistent voters* are chosen randomly and independently for each election.

#### Voting
- Voters sign the election ID and the EB hash with their $sk$.  
- Each vote includes the election ID, the EB hash, and the corresponding signature.  
- Persistent votes additionally include an epoch-specific identifier of the stake pool.  
- Non-persistent votes include the Pool ID and an eligibility signature on the election ID.

#### Certificate Generation
- Upon receiving votes, both voter identities and their signatures are verified.  
- Non-persistent votes are further validated for eligibility.  
- Once a quorum of valid votes is collected, a certificate can be generated.  
- The certificate includes:  
  - The election ID and the message (the hash of the EB)  
  - The identities of participating voters  
  - Eligibility proofs for non-persistent voters  
  - An aggregate signature combining all individual voter signatures

### Requirements

The voting and certificate scheme in Leios must satisfy key requirements to ensure security, efficiency, and practical deployability.

Key registration should be lightweight, requiring minimal data exchange or coordination among participants. 
Ideally, it should be integrated into the existing operational certificate framework to keep certificates compact and avoid unnecessary complexity.

Periodic rotation of cryptographic keys for signing Leios votes and certificates is unnecessary. 
The timing of voting rounds and the key rotation already present in Praos provide sufficient protection against replay and key compromise attacks.

Deterministic signatures, while useful against weak randomness, are not required for Leios. 
Deterministic randomness is only essential in the lottery mechanism, which is securely implemented through VRFs.

The voting committee must be selected locally and unpredictably to resist adversarial interference.
The process should not be overly deterministic or publicly visible, preventing targeted attacks such as denial-of-service or node subversion. 
The protocol must also preserve liveness and soundness—adversaries with significant stake (e.g., over 35%) should not block honest quorums, and even near-majority holders (around 49%) must be unable to form malicious ones.

Because voting occurs frequently and adds notable network load, votes and certificates must remain compact. 
The large size of Praos KES signatures makes them unsuitable, highlighting the need for more space-efficient schemes that fit easily within Praos blocks while leaving room for other transactions.

Lastly, the cryptographic operations for eligibility verification, vote generation, and certificate validation must be highly efficient. 
The total workload should stay well within the CPU budget for Leios stages, ensuring strong performance and scalability under real-world conditions.

### Design Choices

Several certificate schemes were evaluated for Leios, including ALBA variants, SNARK-based voting schemes, and BLS-based certificates, with the goal of identifying a design that best satisfies the security, efficiency, and deployability requirements described above. 
After comparison, BLS certificates based on the *Fait Accompli* sortition scheme were selected as the preferred approach. 
Although this choice requires the registration of additional keys and occasional key rotation, it provides a strong balance between efficiency and practicality, producing certificates smaller than 10 kB.

Other voting mechanisms could be considered preferable if they met the following conditions: no need for new key registration (i.e., reusing existing VRF and KES keys for voting), a certificate size well below the 90,112-byte limit of a Praos block, and proof generation and verification times that remain within the CPU budget of the `cardano-node`. 
However, among the schemes analyzed, BLS certificates offered the most favorable trade-offs across these dimensions.

The BLS voting mechanism relies on a pairing-based signature scheme defined over the BLS12-381 elliptic curve. 
This approach is advantageous because it enables the aggregation of public keys and signatures, allowing large groups of participants to collectively signal approval through a single compact artifact. 
Beyond Leios, the BLS mechanism is also relevant to other Cardano subsystems; Mithril already employs BLS-based aggregation, and Peras is expected to adopt a similar approach in future implementations.

#### Choice of BLS Variant

BLS12-381 signatures can be instantiated in two variants that differ only in which group is used for public keys and which is used for signatures. Both variants are equivalent in security and share the same API surface; they differ only in the size of the encoded artifacts:
- **MinPk variant**: public keys are 48 bytes, signatures are 96 bytes, and a proof of possesion is 2 times 96 bytes.
- **MinSig variant**: signatures are 48 bytes, public keys are 96 bytes, and a proof of possesion is 2 times 48 bytes.
This creates a straightforward trade-off: either public keys are smaller (MinPk) or signatures are smaller (MinSig).

For Leios, this choice affects the size of voting certificates, which in turn impacts bandwidth, storage, and block propagation. Note that proofs of possession are only used at key registration time, so their size has negligible impact on steady-state bandwidth, storage, or verification costs. They therefore do not weigh into the choice between the two variants.

The certificate scheme we use follows the one defined in CIP-0164 together with the more detailed description in
[Specification.md](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/Specification.md) (section *“BLS certificate scheme”*). At a high level, a certificate records:

- the **election identifier** (8 bytes) and **EB hash** (32 bytes),
- a **bitset of persistent voters**, of size \(m / 8\) bytes,
- for each **non-persistent voter**:
  - the Pool ID (28 bytes),
  - its **eligibility proof**, an individual BLS signature of size S_sig,
- one **aggregate vote signature** on the EB (a single BLS signature of size S_sig).

A key point is that **eligibility proofs remain non-aggregated**: the block producer must be able to verify each proof individually against the Fait-Accompli sortition condition. Only the vote signatures on the EB are aggregated.

Under these assumptions, the total certificate size (ignoring small CBOR overhead) is

\[
certificate_bytes = 40 + 2 * S_sig + m / 8 + (28 + S_sig) * (n - m).
\]

Current sortition simulations tune the number of non-persistent seats to roughly 100 across the committee sizes we care about. Concretely, we assume:
- for n = 500, we have m ≈ 400 persistent voters,
- for n = 1000, we have m ≈ 900 persistent voters,

so in both cases (n - m) ≈ 100 non-persistent voters, and the term (28 + S_sig) * (n-m) dominates.

**Quantitative comparison**

For a 1000-seat committee with m ≈ 900 persistent voters:

- **MinSig**:

  \[ certificate_bytes = 40 + 2 * 48 + 113 + (28 + 48) * 100 = 136 + 113 + 7600 = 7849 bytes.
  \]

- **MinPk**:

  \[ certificate_bytes = 40 + 2 * 96 + 113 + (28 + 96) * 100 = 232 + 113 + 12400 = 12745 bytes.
  \]

So, for n = 1000 and \(n - m ≈ 100\), MinPk certificates are about 4.9 kB larger, which is roughly a **60% increase** over MinSig.

We also evaluated the 500-seat case. The percentage increase from MinSig to MinPk is essentially the same (~60%).

**Interpretation for Leios**

- With MinSig, certificates stay comfortably below **8 kB** and keeps certificate propagation and storage lightweight.
- With MinPk, certificates grow to around **12.7 kB**, still within Praos limits but significantly heavier for bandwidth, storage, and diffusion—especially given the number of certificates the system will handle over time.
- Since Leios produces far more **signatures** (votes and eligibility proofs) than public keys, the overall cost is driven by signature size rather than key size.

In summary, the Leios cryptography design therefore **fixes MinSig as the BLS12-381 variant**.

### Implementation Plan

To implement the linear Leios design, efficient BLS signature functionality is essential for achieving fast and compact certificate generation. 
With the adoption of [CIP-0381](https://cips.cardano.org/cip/CIP-0381), `cardano-base` already provides foundational utilities for BLS operations, offering a solid basis for this integration. 
Building on these capabilities, the implementation plan introduces additional bindings and helper modules to ensure smooth interaction with the Leios protocol within the Haskell node. 

This section presents the implementation plan for extending `cardano-base` with BLS signature support and outlines the modifications required to satisfy Leios-specific needs. 
The requirements are organized into two main categories: **core functionality**, which defines the essential BLS operations needed, and **performance and quality**, which ensures the implementation meets the expected efficiency, reliability, and maintainability standards.

#### Core functionality
- **BLS types** 
  - The `BLS12_381.Internal` module in `cardano-base` already provides a comprehensive set of types designed for safe interaction with the linked C functions from the `blst` library. 
  - As part of the integration effort, it is necessary to evaluate which additional types should be introduced beyond those already defined, ensuring full support for the BLS functionality required by Leios.

- **Key generation** 
  - Secure key generation must ensure strong randomness and resilience against side-channel attacks. To achieve this, an integration with the `blst` library through a FFI is required. This involves adding the necessary foreign function imports to the `BLS12_381.Internal` module and implementing the corresponding `SecretKey` type to enable safe and efficient handling of secret keys within the Haskell environment.
  - The `blst` library exposes a key-generation function [`blst_keygen`](https://github.com/supranational/blst/blob/e7f90de551e8df682f3cc99067d204d8b90d27ad/bindings/blst.h#L330) 
    ```C
    void blst_keygen(blst_scalar *out_SK, const byte *IKM, size_t IKM_len, const byte *info DEFNULL, size_t info_len DEFNULL);
    ```
    which derives a secret key from input keying material (IKM) and optional `info`. To use this safely in `cardano-base`, we need to clarify the security guarantees of this construction: what qualifies as a cryptographically secure IKM (length, entropy, generation source) and how `info` should be used (additional entropy vs. domain/context bytes). In parallel, we should examine how `cardano-base` currently sources seeds for other schemes in the `DSIGN` class, review the `blst` keygen C implementation to assess robustness and side-channel posture, align our requirements with the IETF BLS draft’s guidance on key generation (see the “KeyGen” section in the CFRG draft), and determine whether `info` is treated as entropy input or merely contextual/domain-separation data; documenting these findings will let us standardize secure IKM generation and `info` usage for BLS within `cardano-base`.

- **Proof-of-Possession** 
  - The `blst` C library does not provide a direct interface for generating a proof of possession ($PoP$). 
  - This functionality must be implemented manually in `cardano-base`, leveraging the existing `blst` bindings and will be exposed as part of the BLS signing interface.
  - For each BLS keypair `(sk_bls, pk_bls)`, let `pk_bytes` be the canonical compressed encoding of `pk_bls`.  
  - The PoP is defined as a BLS signature over the fixed message: `msg_pop = “PoP” || pk_bytes` where `"PoP"` is a fixed ASCII tag. This ensures that PoP messages are clearly separated from vote messages and cannot be confused with them.
  - PoP generation and verification are performed through dedicated PoP helper functions in the BLS signing module. Although the exact API shape differs by implementation language, the logical interface follows:
    ```
    pop  = derive_pop(sk_bls, context_pop)
    ok   = verify_pop(pk_bls, pop, context_pop)
    ```
    where `context_pop` provides the domain-separation settings (e.g., DST).
  - The PoP and vote-signature domains must be distinct.  
Leios **must** use a PoP-specific domain separation tag (`DST_POP`) that differs from the tag used for vote signatures (`DST_VOTE`).  
This prevents PoPs from being repurposed as votes and preserves the security separation between registration and voting.
  - The current BLS implementation in Cardano uses the base domain-separation tag: `“BLS_DST_CARDANO_BASE_V1”`

    For Leios, we recommend deriving protocol-specific DSTs from this base value, for example:
    ```
    DST_POP  = “BLS_DST_CARDANO_BASE_LEIOS_POP_V1”
    DST_VOTE = “BLS_DST_CARDANO_BASE_LEIOS_VOTE_V1”
    ```

- **Public key derivation** 
  - Implement deterministic derivation of the public key ($pk$) from the corresponding secret key ($sk$) for the selected BLS variant. 
  - This requires adding a FFI binding to the `blst` library to enable secure and efficient key derivation within `cardano-base`.
    ```C
    void blst_sk_to_pk_in_g1(blst_p1 *out_pk, const blst_scalar *SK);
    void blst_sk_to_pk_in_g2(blst_p2 *out_pk, const blst_scalar *SK);
    ```

- **Signature** 
  - Implement signature generation and verification APIs that are variant-agnostic and support domain separation, with DST supplied by the caller. This functionality requires integrating with the `blst` library through FFI bindings, using the following functions:
    ```C
    void blst_sign_pk_in_g1(blst_p2 *out_sig, const blst_p2 *hash, const blst_scalar *SK);
    void blst_sign_pk_in_g2(blst_p1 *out_sig, const blst_p1 *hash, const blst_scalar *SK);
    ```
    For single-signature verification, correctness can be established through a standard pairing check between the signature, message hash, and public key. See [this](https://www.ietf.org/archive/id/draft-irtf-cfrg-bls-signature-05.html#name-verify).

- **Aggregation** 

  The Leios EB certificate contains a single aggregated BLS signature over the message 
  ```
  msg_vote = (election_id, EB_hash)
  ```
  All valid votes from both **persistent** and **non-persistent** voters can be combined into the same aggregated signature.

  - **Persistent voters**  
  These are always eligible and require only their public key and signature.

  - **Non-persistent voters**  
  These voters succeed in a sortition and must also provide an eligibility proof.  
 
  To support this functionality, several helper functions should be implemented:
  - A function to aggregate multiple public keys into a single aggregated key.  
  - A function to aggregate multiple signatures into a single aggregated signature.  
  - A function that, given a message and multiple $(pk, sig)$ pairs over that message, performs batch verification.

  The first two functions are particularly useful for building an accumulator that locally tallies Leios votes and aggregates them in advance for block production. The third provides a one-shot approach for efficient verification. Since the optimal aggregation strategy depends on when and how votes are combined, all three functions should be implemented to support flexible and efficient use within Leios.

- **Batch verification** 
  - Implement a batch verification API to efficiently verify multiple $(pk, msg, sig)$ tuples. 
  - This requires adding FFI bindings to the `blst` library. 
  - The underlying C functions can be composed to load multiple $(pk, msg, sig)$ combinations into a single pairing context for verification. 
  - When many of the messages are identical, it becomes more efficient to merge them beforehand. 
    - It is advisable to use a key-value data structure where each $msg$ serves as the key, and the corresponding values are the multiple $(pk, sig)$ pairs that can be aggregated using the existing aggregation functions.

- **DSIGN integration**
  - Integrate the internal BLS signature implementation into the `DSIGN` class. 
  - Once completed, the `cardano-base` module `BLS12_381.Internal` will expose a comprehensive set of utility functions for setting up and managing the BLS signature scheme—similar to how `DSIGN.Ed25519` provides utilities for Ed25519 signatures. 
  - End users will not interact directly with this low-level API but will instead use the higher-level `DSIGN` class interface. 
  - As part of this integration, a new `DSIGN` instance must be defined for BLS signatures, specifying the minimal required functions and their corresponding type signatures.

- **Serialization**
  - Implement deterministic serialization by providing `ToCBOR` and `FromCBOR` instances, as well as raw byte encodings for keys and signatures. 
  - Enforce strict validation through length, subgroup membership, and infinity checks.
  - Ensure canonical compressed encodings following the Zcash standard for BLS points.

- **Conformance vectors**
  - Add conformance tests using test vectors from the initial Rust implementation to ensure cross-impl compatibility.

#### Performance and quality
- **Performance benchmarks**
  - Benchmark single-verify, aggregate-verify, and batch-verify; report the impact of batching vs individual verification.
  - Ensure that certificate generation and certificate verification both fit comfortably within protocol deadlines.
  - Provide comparable measurements across implementations (Haskell, Rust, and future node variants).
  - Track performance evolution over time on stable, dedicated hardware.

- **Rust parity**
  - Compare performance against the Rust implementation; document gaps and ensure functional parity on vectors.

- **Determinism portability**
  - Deterministic results across platforms/architectures; outputs independent of CPU feature detection.

- **Documentation**
  - Document the outward facing API in cardano-base and provide example usages. Additionally add a section on do's and don'ts with regards to security of this scheme outside the context of Leios.

#### Other utilities
- Registration: See [this](https://github.com/input-output-hk/ouroboros-leios/blob/d5f1a9bc940e69f406c3e25c0d7d9aa58cf701f8/crypto-benchmarks.rs/Specification.md#key-registration)
- Sortition: See [this](https://github.com/input-output-hk/ouroboros-leios/blob/d5f1a9bc940e69f406c3e25c0d7d9aa58cf701f8/crypto-benchmarks.rs/Specification.md#sortition)

#### Implementation notes
- The $PoP$ verification is likely performed at the certificate level; therefore, the API described above should not handle it directly.  
  - The existing `BLS12_381` code already abstracts over both $G_1$ and $G_2$ curves, and this abstraction should be preserved.  
- The `blst` library provides optimized verification for multiple messages, signatures, and public keys using a combined pairing check.  
  - While this functionality could offer performance benefits, it remains uncertain whether it will be necessary for linear Leios, where such batch verification may not provide a meaningful speedup.

### Potential Risks and Mitigations

> [!WARNING]
>
> TODO: Contribution from crypto team.

### Roadmap

> [!WARNING]
>
> TODO: Contribution from crypto team.

This roadmap outlines the planned tasks and milestones for integrating BLS functionality into `cardano-base` to support the Leios protocol. 
The implementation is divided into three delivery cycles, progressing from foundational FFI bindings to high-level integration and code audit.

#### Core Bindings and Setup
<!-- Delivery cycle 1 -->
*Establish the foundational Haskell ↔ C interoperability layer for BLS operations.*
- Create Haskell ↔ C Bindings for the following functionalities:
  - Key generation,
  - Public key derivation,
  - Signature generation and verification.
- Create Haskell Function for Proof-of-Possession functionality using existing `blst` primitives.  

#### Extended Functionality and Security Review
<!-- Delivery cycle 2 -->
*Build higher-level cryptographic utilities, perform security validation, and finalize BLS type definitions.*
- Define and Add New Types: Identify and introduce any missing types needed for safe and ergonomic BLS operations.
- Create Haskell ↔ C Binding for batch verification support for efficient validation of multiple $(pk, msg, sig)$ triples.
- Create Haskell Function for aggregation logic for multiple signatures and public keys to enable compact certificates.  
- Check Security of key generation function of the C implementation and assess its adherence to the IETF BLS standard for secure IKM handling.  

#### Integration and Quality Assurance
<!-- Delivery cycle 3 -->
*Integrate BLS signatures into the `DSIGN` class and complete final review.*
- Add Internal BLS Signature to `DSIGN` Class  
- Audit the Code

## Performance & Tracing (P&T)

> [!WARNING]
>
> TODO: Mostly content directly taken from [impact analysis](../ImpactAnalysis.md). Expand on motivation and concreteness of changes. We could also consider merging performance engineering aspects into respective layers/components. This also feels a bit ouf of touch with the [implementation plan](#implementation-plan); to be integrated better for a more holistic quality and performance strategy. See also https://github.com/input-output-hk/ouroboros-leios/pull/596 for more notes on performance & tracing.

This outlines Leios impact on the node's tracing system and on dedicated Leios performance testing and benchmarks.

### Tracing

Leios will require a whole new set of observables for a Cardano node, which do not exist for Praos. These observables will need to be exposed - just as the existing ones - via trace evidence and metrics. A specification document will need to be created and maintained, detailing the semantics of those new observables. Some might be specific to the Haskell implementation, some might be generic to any Leios implementation. The work from R&D and the insights gained from Leios simulations will be the input to that document.

During Leios implementation process, P&T will need to oversee that traces are emitted at appropriate source locations wrt. their semantics, as well as properly serialized or captured in a metric in `cardano-node` itself. P&T analysis tooling - mostly the `locli` package - will need significant adjustment to parse, process and extract meaningful performance data from raw trace evidence.

### Performance testing

For a systematic approach to benchmarking, all Leios modes of operation and their respective configurations will need to be captured in P&T's benchmark profile library - the `cardano-profile` package. P&T's `nix` & `Nomad` based automations need to be adjusted to deploy and execute Leios profiles as benchmarks from that library.

On a conceptual level, the challenge to benchmarking Leios - being built for high throughput - is putting it under a stable saturation workload for an extended period of time. By stable, I'm referring to maintaining equal submission pressure over the benchmark's entire duration. These workloads need to be synthetic in nature, as only that way one can reliably and consistently stress specific aspects of the implementation. For Praos benchmarks, they're created dynamically by `tx-generator`. New workloads will need to be implemented, or derived from the existing ones.

Considering all the above, the most promising approach would be finding a model, or symmetrically scaled-down Leios, which is able to reliably predict performance characteristics of the non-scaled down version - exactly as P&T's benchmarking cluster hardware models a larger environment like `mainnet` at scale and is able to predict performance impact based on observations from the cluster. By Leios version above, I'm of course referring to the exact same Leios implementation whose performance characteristics are being measured. Model or scaled versions will have to be realized via configuration or protocol parameters exclusively.

Any Leios option or protocol parameter that allows for sensibly scaling the implementation has to be identified. This will allow for correlating observed performance impact or trade-offs to e.g. linearly scaling some parameter. Comparative benchmarking will require a clearly structured process of integrating new features or changes into the implementation. When many changes are convoluted into one single benchmarkable, it gets increasingly difficult to attribute an observation to a single change - in the worst case, an optimization can obscure a regression when both are introduced in the same benchmarkable.

Finding a model / scaled Leios version is an iterative process which requires continuous validation. It will require P&T to be in constant, close coordination with both implementors and researchers.

## End-to-end testing

> [!WARNING]
>
> TODO: Mostly content directly taken from [impact analysis](../ImpactAnalysis.md). Expand on motivation and concreteness of changes. This also feels a bit ouf of touch with the [implementation plan](#implementation-plan); to be integrated better for a more holistic quality and performance strategy.

The [cardano-node-tests](https://github.com/IntersectMBO/cardano-node-tests) project offers test suites for end-to-end functional testing and mainnet synchronization testing.

The end-to-end functional test suite checks existing functionalities. It operates on both locally deployed testnets and persistent testnets such as Preview and Preprod. With over 500 test cases, it covers a wide spectrum of features, including basic transactions, reward calculation, governance actions, Plutus scripts and chain rollback.

Linear Leios primarily impacts the consensus component of `cardano-node`, leaving end-user experience and existing functionalities unchanged. Consequently, the current test suite can largely be used to verify `cardano-node`'s operation after the Leios upgrade, requiring only minor adjustments.

### New end-to-end tests for Leios

New end-to-end tests for Leios will focus on two areas:

- Hard-fork testing from the latest mainnet era to Leios
- Upgrading from the latest mainnet `cardano-node` release to a Leios-enabled release

### New automated upgrade testing test suite

The suite will perform the following actions:

1. **Initialize Testnet** - Spin up a local testnet, starting in the Byron era, using the latest mainnet `cardano-node` release.
2. **Initial Functional Tests** - Run a subset of the functional tests.
3. **Partial Node Upgrade** - Upgrade several block-producing nodes to a Leios-enabled release.
4. **Mid-Upgrade Functional Tests** - Run another subset of the functional tests.
5. **Cooperation Check** - Verify seamless cooperation between nodes running the latest mainnet `cardano-node` release and those running a Leios-enabled release on the same testnet.
6. **Full Node Upgrade** - Upgrade the remaining nodes to a Leios-enabled release.
7. **Leios Hard-Fork** - Perform the hard-fork to Leios.
8. **Post-Hard-Fork Functional Tests** - Run a final subset of the functional tests.


## Node-to-client

> [!WARNING]
>
> TODO: concrete discussion on how the `cardano-node` will need to change on the N2C interface, based on [client interfaces](#client-interfaces)
>
> - Mithril, for example, does use N2C `LocalChainSync`, but does not check hash consistency and thus would be compatible with our plans.


# Glossary

| Term                       | Definition                                                            |
|----------------------------|-----------------------------------------------------------------------|
| **RB**                     | Ranking Block - Extended Praos block that announces and certifies EBs |
| **EB**                     | Endorser Block - Additional block containing transaction references   |
| **CertRB**                 | Ranking Block containing a certificate                                |
| **TxRB**                   | Ranking Block containing transactions                                 |
| **BLS**                    | Boneh-Lynn-Shacham signature scheme using elliptic curve cryptography |
| **BLS12-381**              | Specific elliptic curve used in cryptography                          |
| **PoP**                    | Proof-of-Possession - Prevents rogue key attacks in BLS aggregation   |
| **$L_\text{hdr}$**         | Header diffusion period (1 slot)                                      |
| **$L_\text{vote}$**        | Voting period (4 slots)                                               |
| **$L_\text{diff}$**        | Certificate diffusion period (7 slots)                                |
| **FFD**                    | Freshest-First Delivery - Network priority mechanism                  |
| **ATK-LeiosProtocolBurst** | Attack where adversary withholds and releases EBs simultaneously      |

# References

> [!WARNING]
> TODO: Use pandoc-compatible citations https://pandoc.org/MANUAL.html#citation-syntax

1. **CIP-164**: Ouroboros Linear Leios - Greater transaction throughput https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md

1. **Leios Impact Analysis**: High-level component design https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/ImpactAnalysis.md

1. **Leios Formal Specification**: Agda implementation https://github.com/input-output-hk/ouroboros-leios/tree/main/formal-spec

1. **Cardano Ledger Formal Specification**:
   https://github.com/IntersectMBO/formal-ledger-specifications/

1. **Ouroboros Peras Technical Design**: Finality improving consensus upgrade https://tweag.github.io/cardano-peras/peras-design.pdf

1. **Ouroboros Genesis**: Bootstrap mechanism https://iohk.io/en/research/library/papers/ouroboros-genesis-composable-proof-of-stake-blockchains-with-dynamic-availability/

1. **Ouroboros Network Specification**:
   https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf

1. **UTxO-HD Design**:
    https://github.com/IntersectMBO/ouroboros-consensus/blob/main/docs/website/contents/for-developers/utxo-hd/index.md
