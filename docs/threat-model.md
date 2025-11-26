---
title: Leios threat model
status: Draft
version: 0.3
author:
  - Sebastian Nagel <sebastian.nagel@iohk.io>
---

A threat model for the Leios consensus change for Cardano as proposed in [CIP-164](https://github.com/cardano-foundation/CIPs/pull/1078). This model is considered in the [Leios design document](./leios-design), which holds more more details on the implementation plan and technical design decisions.

### Document history

This document is a living artifact and will be updated as implementation progresses, new risks are identified, and validation results become available. Reviews and updates should happen:

- Before each major protocol upgrade
- After any security incidents
- Quarterly during active development
- When new attack vectors are discovered

| Version | Date       | Changes                                                               |
|---------|------------|-----------------------------------------------------------------------|
| 0.3     | 2025-11-26 | Major restructure, grouped threats into categories, changed numbering |
| 0.2     | 2025-08-05 | Update to Linear protocol variant, added honey pot attack vector      |
| 0.1     | 2025-07-17 | Initial draft using EB-only protocol variant                          |

Besides past versions of this document, see also the [threat model section in Leios Technical Report #1](./technical-report-1.md#threat-model) and more [comments on attack surface in Leios Technical Report #2](./technical-report-2.md#notes-on-the-leios-attack-surface).

## System Overview

### Description

Leios is an overlay protocol on top of Ouroboros Praos that enhances transaction throughput by allowing block producers to create larger Endorser Blocks (EBs) alongside standard Praos blocks (enhanced as Ranking Blocks - RBs). The system maintains backward compatibility while introducing new responsibilities for stake pools.

### Key Components

#### Entities

- **Mempool**: List of valid, pending transactions that could be added to the chain. Expanded capacity to support both RB and EB production
- **Ranking Block (RB)**: Standard Praos block enhanced with Leios certificate and EB announcement fields. Limited to current mainnet size (~88 kB)
- **Endorser Block (EB)**: New block type that references transactions for inclusion. May be substantially larger (~640 kB for 20k transaction references)
- **Leios Certificate**: Cryptographic proof about aggregated stake-weighted votes on EB validity and transaction availability

#### Network Protocols
- **Transaction Submission Protocol**: Existing protocol, unchanged except for expanded mempool capacity, served upstream
- **Chain Sync Protocol**: Existing protocol for tracking block headers of currently selected chain, served downstream
- **Block Fetch Protocol**: Existing protocol for downloading blocks, served downstream
- **EB Announcement Protocol**: New protocol to gossip EB existence, served downstream
- **EB Fetch Protocol**: New protocol for retrieving EBs on-demand, served downstream
- **Transaction Fetch Protocol**: New protocol for retrieving transactions referenced by EBs, served downstream
- **Vote Diffusion Protocol**: New protocol for propagating votes on EBs, served downstream

#### Roles
- **Block Producers**: Produce RBs and simultaneously create EBs, participate in voting
- **Relays**: Participate in transaction, block, and vote diffusion
- **Clients**: Submit transactions and observe ledger state, maintain backward compatibility

#### System Flow
1. **Block Production**: When eligible, stake pools simultaneously create an RB (announcing an EB) and the corresponding EB
2. **EB Distribution**: EBs are discovered via RB headers and fetched by nodes
3. **Committee Validation**: Selected voting committee validates EBs
4. **Certification**: EBs achieving quorum (>60% voting stake) become certified
5. **Chain Inclusion**: Certificates are included in subsequent RBs, making referenced transactions part of the ledger

See also the [CIP draft](https://github.com/input-output-hk/ouroboros-leios/pull/396) for a more detailed specification.

## Assets to Protect

For each asset we define what could be impacted in respect to its Confidentiality, Integrity, Availability; i.e. the [CIA Triad](https://www.splunk.com/en_us/blog/learn/cia-triad-confidentiality-integrity-availability.html)

### A1: Blockchain Safety
The fundamental guarantee that all honest nodes agree on the blockchain history and no conflicting valid chains exist.

**CIA Impact**
- **Confidentiality**: Not applicable - blockchain is public
- **Integrity**: CRITICAL - Chain splits or conflicting histories would break consensus
- **Availability**: HIGH - Safety failures could halt the network indefinitely

**Leios-Specific Considerations**: Leios is an overlay protocol and relies on the safety (and liveness) of the underlying consensus protocol: Praos. Safety in Praos, also called persistence, is guaranteed if the Delta assumption holds and honest stake exceeds 50%. Hence, any of the Leios-specific mechanisms (EB creation, voting, certificate inclusion) must not delay Praos blocks consistently.

### A2: Blockchain Liveness
The guarantee that the blockchain continues to make progress by producing new blocks and processing transactions within reasonable time bounds.

**CIA Impact**
- **Confidentiality**: Not applicable - blockchain is public
- **Integrity**: MEDIUM - Liveness failures don't corrupt existing data but prevent new valid transactions
- **Availability**: CRITICAL - Network becomes unusable if block production stops

**Leios-Specific Considerations**: Analogously to Blockchain Safety, EB creation, voting, and certificate inclusion must not prevent Praos block production from making progress. Any mechanisms that prevent production - by protocol, or practically, also temporarily - can lead to loss of liveness.

### A3: Transaction Validity, Availability, and Determinism
All transactions included in the blockchain must be cryptographically valid, available to all network participants for verification, and deterministic (transactions only consume fees if successfully included, a key Cardano property).

**CIA Impact**
- **Confidentiality**: Not applicable - transactions are public once included
- **Integrity**: CRITICAL - Invalid transactions would corrupt the ledger state; non-deterministic behavior would break fee guarantees
- **Availability**: HIGH - Unavailable transactions prevent proper validation and syncing

**Leios-Specific Considerations**: EBs reference transactions that must be available when the EB is processed; voting nodes must verify transaction availability before voting; deterministic behavior must be preserved across the EB endorsement and certification process.

### A4: Operational Sustainability
Computational and network resources consumed by Stake Pool Operators to participate in the protocol, including CPU, memory, storage, and bandwidth. Resource increases are acceptable as long as they are covered by corresponding incentives to maintain operational sustainability.

**CIA Impact**
- **Confidentiality**: LOW - Resource usage patterns could reveal some operational information
- **Integrity**: MEDIUM - Resource exhaustion could compromise node operation and validation
- **Availability**: HIGH - Excessive resource usage could force SPOs offline or prevent participation

**Leios-Specific Considerations**: New responsibilities (EB creation, voting, additional network protocols) must not significantly increase SPO operational costs relative to incentives or create barriers to participation.

### A5: Decentralization
The distribution of block production, voting power, and network participation across many independent operators.

**CIA Impact**
- **Confidentiality**: LOW - Centralization patterns are observable but don't directly affect data secrecy
- **Integrity**: HIGH - Centralization increases risk of coordinated attacks on consensus
- **Availability**: HIGH - Centralized infrastructure creates single points of failure

### A6: High Throughput
The enhanced transaction processing capacity that Leios provides beyond basic Praos liveness, enabling the network to handle significantly more transactions per unit time.

**CIA Impact**
- **Confidentiality**: Not applicable - throughput is a performance metric
- **Integrity**: LOW - Reduced throughput doesn't corrupt data but may affect user expectations
- **Availability**: HIGH - Throughput reduction defeats the primary purpose of the Leios upgrade

**Leios-Specific Considerations**: EB certification failures, voting delays, or resource exhaustion attacks directly impact the throughput gains Leios is designed to provide.

## Threats

The Leios protocol may be vulnerable to the following categories of threats. Each category represents fundamental attack surfaces that stem from the protocol's design and operation.

### Praos dependency and VRF-based eligibility

Leios builds upon Ouroboros Praos and inherits both its security properties and potential vulnerabilities.
The VRF (Verifiable Random Function) mechanism that determines block production eligibility in Praos also governs EB creation and voting committee selection in Leios.
The fundamental threat is that adversaries can manipulate the randomness generation process to gain unfair advantages in leader election, potentially concentrating block production and voting power.

VRF grinding attacks involve adversaries using computational resources to try multiple VRF evaluations and selectively revealing only favorable outcomes.
As described in [CPS-0021](https://github.com/nhenin/CIPs/tree/CIP-Ouroboros-Phalanx/CPS-0021), this manipulation becomes more viable with >20% total stake and can enable various attacks including private forking, selfish mining, and censorship.
In Leios, successful grinding would allow attackers to increase their probability of EB creation opportunities and voting committee selection beyond their proportional stake.

**Impact**: VRF manipulation can concentrate EB production and voting power, undermining the decentralization that Leios depends on for security. This amplification effect is particularly dangerous because Leios relies on diverse participation for both block production and voting-based certification. Successful grinding attacks enable secondary attacks like private forking, where adversaries can build longer chains in secret, and selective censorship through concentrated block production control. A compromise of VRF keys has a similar effect of giving the attacker more block production opportunities than they would normally have.

**Assets Affected**: Blockchain Safety, Decentralization

**Mitigation**:
  - Leios security is fundamentally tied to Praos security.
  - Amplify costs of VRF grinding Ouroboros Phalanx ([CIP-0161](https://github.com/nhenin/CIPs/tree/CIP-Ouroboros-Phalanx/CIP-0161)), which introduces computational cost amplification to make grinding attacks economically infeasible by increasing grinding costs by approximately 10^10 while maintaining lightweight computation for honest participants.
  - Standard key management practices protect against VRF key compromise.

| #  | Method                             | Effect                                    | Resources                      | Mitigation            |
|----|------------------------------------|-------------------------------------------|--------------------------------|-----------------------|
| T1 | Any threat to Praos                | Leios is only as secure as Praos          | -                              | Dependency on Praos   |
| T2 | VRF grinding on EB eligibility     | Increased probability of EB creation      | CPU, stake (>20%)              | Ouroboros Phalanx R&D |
| T3 | VRF grinding on voting eligibility | Increased probability of voting selection | CPU, stake (>20%)              | Ouroboros Phalanx R&D |
| T4 | VRF key compromise                 | Unfair advantage in eligibility           | Very high cryptographic attack | Strong key management |

### Equivocation

In Leios, block producers and voters are only allowed one production per VRF lottery win for EBs and votes respectively. Equivocation occurs when malicious actors create multiple conflicting EBs or votes and diffuse them to different network segments, attempting to disrupt the protocol or gain unfair advantages. Equivocation detection mechanisms were already considered in the original Leios paper and are part of the protocol specification.

A particularly interesting case involves BLS key compromise for voting. When a BLS private key used for voting is compromised, legitimate key holders can intentionally equivocate (create conflicting votes) as a defensive measure until key rotation takes effect. This "defensive equivocation" invalidates both honest and adversarial votes signed by the compromised key, preventing the attacker from using the key maliciously while minimizing protocol disruption.

**Impact**: EB equivocation wastes network resources as nodes must process multiple conflicting blocks, only one of which can be valid. Vote equivocation can interfere with certificate creation and force nodes to choose between conflicting certificates. Double voting (voting on multiple conflicting EBs for the same voting period) can enable multiple certificates for conflicting transaction sets, wasting bandwidth and processing resources. However, the protocol's design limits the impact through equivocation detection and the principle that only RB inclusion affects chain selection, not certificate existence alone.

**Assets Affected**: Operational Sustainability, High Throughput

**Mitigation**: The Leios protocol specification includes explicit equivocation detection mechanisms that identify misbehaving nodes and equivocation proofs are forwarded through the network. For BLS key compromise, key rotation procedures enable recovery while defensive equivocation provides interim protection. Double voting has limited safety impact since multiple certificates can exist but only RB inclusion determines chain progression.

| #  | Method             | Effect                                | Resources                    | Mitigation                               |
|----|--------------------|---------------------------------------|------------------------------|------------------------------------------|
| T5 | EB equivocation    | Lower throughput, resource waste      | Stake for block production   | Equivocation detection per Leios design  |
| T6 | Vote equivocation  | Interfere with certificate creation   | Stake for voting eligibility | Equivocation detection per Leios design  |
| T7 | Double voting      | Multiple certificates, resource waste | Stake for voting eligibility | Chain selection prioritizes RB inclusion |
| T8 | BLS key compromise | Unauthorized vote creation            | Cryptographic attack         | Key rotation, defensive equivocation     |

### Inaction and Nuisance

Producer nodes might attempt to disrupt the protocol by failing to play their assigned role or by creating invalid information. This includes declining to create EBs when entitled, declining to vote when eligible, or creating invalid EBs or votes. More serious variants involve certificate manipulation - including invalid certificates in RBs or attempting to cryptographically forge certificates without sufficient votes. The latter represents a fundamental attack on the protocol's cryptographic foundations and would indicate a severe compromise of the BLS signature scheme used for vote aggregation.

The incentive structure of Leios is designed such that most inaction attacks are self-defeating - nodes that decline to participate receive fewer rewards albeit very indirectly. Creating invalid blocks or votes wastes the attacker's own eligibility while create a minor annoyance to their first downstream nodes by burdening them with useless verification work, but the cryptographic aspects of Leios quickly catch and discard invalid submissions.

**Impact**: These attacks primarily reduce protocol throughput rather than compromising safety. Invalid submissions create computational overhead for validation but are quickly detected and discarded. The economic incentives generally discourage such behavior since attackers forfeit their own rewards while providing minimal disruption to the network.

**Assets Affected**: High Throughput, Operational Sustainability

**Mitigation**: The protocol's incentive structure provides the primary defense - participants who don't fulfill their roles receive proportionally reduced rewards. Cryptographic validation quickly identifies and discards invalid submissions to avoid assymetric resource attacks. The voting committee mechanism in Leios provides additional resilience by requiring multiple participants for EB certification, so individual node inaction has limited impact.

> [!WARNING]
>
> TODO: Move certificate forging somewhere else as it is quite different?

| #   | Method                               | Effect                           | Resources                    | Mitigation                               |
|-----|--------------------------------------|----------------------------------|------------------------------|------------------------------------------|
| T9  | Decline to create EB                 | Lower throughput                 | Stake for block production   | Reduced rewards                          |
| T10 | Decline to vote                      | Lower throughput                 | Stake for voting eligibility | Reduced rewards                          |
| T11 | Create invalid EB                    | Lower throughput, resource waste | Stake for block production   | Reduced rewards, validate before forward |
| T12 | Create invalid vote                  | Lower throughput, resource waste | Stake for voting eligibility | Reduced rewards, validate before forward |
| T13 | Reference invalid transactions in EB | Lower throughput, resource waste | Stake for block production   | Reduced rewards, validate before forward |
| T14 | Include invalid certificate in RB    | Lower throughput, resource waste | Stake for block production   | Certificate verification                 |
| T15 | Forge certificate without quorum     | Manipulate transaction inclusion | Cryptographic attack         | Strong BLS cryptography                  |

### Omission and Manipulation

Block producers have control over which transactions to include in their EBs and can exploit this power for censorship (omission) or value extraction (manipulation). In Linear Leios, the coupled RB/EB production model gives every block producer opportunities to manipulate transaction ordering and selection within the EB they create alongside their RB.

This creates opportunities for front-running, where producers observe profitable transactions in the mempool and either reorder them for advantage or insert their own competing transactions. Censorship attacks involve deliberately omitting specific transactions to prevent their execution, though the mempool design limits effectiveness since omitted transactions will likely appear in subsequent honest blocks.

SPOs concerned about front-running competition may choose to bypass the EB mechanism entirely and include transactions directly in their RBs, avoiding exposure of these tranactions by the endorsement process. This reduces overall network throughput but provides some protection against MEV extraction by other producers. However, this strategy becomes self-limiting when transaction load exceeds Praos-only capacity, forcing delays upon these transactions and risking being front-run themselves.

**Impact**: These attacks primarily affect transaction fairness and market efficiency rather than protocol safety. Transaction reordering has limited impact on Cardano due to the EUTxO ledger design, where transactions either succeed or fail independently based on available UTxOs rather than global state changes. However, front-running and MEV extraction remain significant concerns - block producers can observe profitable transactions and may be able to compete with better prices or insert intermediary transactions - depending on application design. Censorship reduces liveness for targeted transactions but cannot permanently prevent inclusion due to the distributed nature of block production and the memory pool mechanism.

**Assets Affected**: Transaction Validity/Availability/Determinism, Decentralization

**Mitigation**: The primary defense is the memory pool design - omitted transactions remain available for inclusion in subsequent honest blocks, limiting censorship effectiveness. The distributed nature of block production means no single actor can permanently censor transactions. Detection of MEV extraction is challenging since legitimate transaction selection and ordering can appear similar to value extraction. Mitigation options are limited since EB opportunities are coupled to RB opportunities and cannot be parameterized separately.

| #   | Method                                      | Effect                                 | Resources                  | Mitigation                                                   |
|-----|---------------------------------------------|----------------------------------------|----------------------------|--------------------------------------------------------------|
| T16 | Omit transactions from EB                   | Lower throughput, temporary censorship | Stake for block production | Memory pool persistence                                      |
| T17 | Reorder transactions in EB                  | MEV, market manipulation               | Stake for block production | Limited detection capability                                 |
| T18 | Insert or replace transactions in EB        | MEV, market manipulation               | Stake for block production | Limited detection capability                                 |
| T19 | Ignore certificates, include txs in RB only | Lower throughput, avoid front-running  | Stake for block production | Reduced rewards, self-limiting when load exceeds RB capacity |

### Data withholding

> [!NOTE]
> This is also a [key threat informing the Leios technical design](./leios-design#data-withholding)

Adversaries deliberately prevent or delay the diffusion of EB transaction data to disrupt the certification process and degrade network throughput. This attack targets the fundamental dependency between transaction availability and EB certification, exploiting the gap between optimistic and worst-case diffusion scenarios that forms the basis of Leios' security argument. Unlike protocol bursts that overwhelm with volume, data withholding attacks manipulate timing and availability of critical data.

The attack operates by controlling when and to whom transaction data becomes available. When an EB is announced via an RB header, voting committee members must acquire and validate the complete transaction closure before casting votes. Adversaries can refuse to serve EB bodies, selectively withhold individual transactions, or strategically time data release to exceed voting deadlines. More sophisticated variants involve network-level manipulation to prevent data from reaching specific voting committee members within the required timeframe.

Advanced network-based variants can target high-stake voting nodes through eclipse attacks, where adversaries control the network connections of specific nodes to manipulate their information flow. Since voting committee membership involves some degree of public information, persistent voting members with significant stake could potentially be identified and targeted. However, eclipsing distinct nodes across a distributed network is non-trivial due to high network connectivity degrees and existing eclipse protection mechanisms.

A particularly dangerous and sophisticated variant targets blockchain safety itself by allowing EBs to achieve certification while preventing timely availability to all honest nodes. The adversary releases data to just enough voting committee members to achieve certification, but not to all network participants. This can create scenarios where certified EBs cannot be processed by honest nodes within the L_diff parameter, potentially violating Praos timing assumptions.

**Impact**: Data withholding primarily reduces throughput when EBs fail certification due to unavailable data, forcing wasted voting resources and delayed transaction processing. Thereotically, there is a high impact variant that can compromise blockchain safety by creating timing violations in Praos diffusion. By reducing the number of honest nodes that receive EB data in time for certification, adversaries also impair subsequent diffusion, making peer-to-peer propagation slower and less reliable. While occasional timing misses are normal in Ouroboros, persistent violations can lead to longer forks and degraded chain quality.

**Assets Affected**: High Throughput (primary), Blockchain Safety (sophisticated)

**Mitigation**: The L_diff parameter is designed to bound the gap between optimistic and worst-case diffusion even under adversarial conditions. The certification mechanism provides defense against stake-based withholding by requiring broad consensus before including EBs in the ledger. Protocol violation enforcement includes mandatory transaction fetch attempts from EB-serving peers, connection pruning with back-off for timeout violations, and multi-peer transaction sourcing as fallback. Network-level attacks require sophisticated countermeasures including redundant peer connections, timeouts for non-responsive nodes, and strategic committee selection. Eclipse protection mechanisms like "ledger peers", high network connectivity degrees, and connection diversity provide significant defense against targeted node isolation. Empirical validation of real-world network conditions against timing assumptions is essential.

> [!WARNING]
>
> TODO: Should this be also about network delays?

| #   | Method                                          | Effect                                             | Resources                              | Mitigation                                               |
|-----|-------------------------------------------------|----------------------------------------------------|----------------------------------------|----------------------------------------------------------|
| T20 | Withhold announced EB or endorsed transactions  | Lower throughput                                   | Stake for block production             | Connection timeouts, peer pruning                        |
| T21 | Selectively withhold data from voting committee | Prevent honest EB certification, reduce throughput | Network position control               | Redundant peer connections, diffusion monitoring         |
| T22 | Selectively withhold data from honest nodes     | Allow certification, delay block propagation       | Network position control, modest stake | L_diff parameter sizing, worst-case diffusion validation |

### Protocol bursts

> [!NOTE]
> This is also a [key threat informing the Leios technical design](./leios-design#protocol-bursts)

Adversaries can withhold large numbers of EBs and their transaction closures over extended periods, then release them simultaneously to create concentrated bursts of network traffic. This attack exploits Leios' requirement that nodes must attempt to acquire any EB correctly announced even if it arrives too late for the node to vote on it, since the EB might still be certified by other nodes and required for future chain selection.

The attack magnitude depends on the adversary's stake proportion and EB size parameters, reaching hundreds of megabytes or even gigabytes of data to be fetched. An adversary controlling 1/3 stake could accumulate approximately 720 EBs over 12 hours, potentially totaling over 9 gigabytes if each EB contains maximum-sized transaction sets. When released simultaneously, this creates sustained bandwidth pressure that can degrade network performance even for nodes that validate only a small subset of the burst.

**Impact**: Protocol bursts target network resources and can escalate from operational issues to safety threats if traffic prioritization is insufficient. While the protocol requires Praos traffic to be prioritized over Leios traffic, imperfect prioritization during large bursts can delay Praos block diffusion beyond the critical timing parameter Δ, potentially compromising blockchain safety. The sheer bandwidth utilization is problematic even when honest nodes validate only a fraction of the burst data. Infrastructure limitations like cloud provider throttling, router buffer saturation, and asymmetric CPU/memory costs amplify the impact and make perfect prioritization challenging.

**Assets Affected**: Operational Sustainability, High Throughput, Blockchain Safety (if prioritization fails)

**Mitigation**: The primary defense is traffic prioritization implementing freshest-first delivery semantics - Praos traffic must be preferred over Leios traffic, and fresh Leios traffic over stale traffic. However, some infrastructural resources cannot be prioritized perfectly, including CPU, memory, disk bandwidth, and network router buffers. The attack's magnitude is bounded by the adversary's stake proportion, but ultimately requires engineering solutions for effective prioritization during burst conditions.

| #   | Method                                    | Effect                                                                     | Resources                      | Mitigation                                      |
|-----|-------------------------------------------|----------------------------------------------------------------------------|--------------------------------|-------------------------------------------------|
| T23 | Withhold then release large number of EBs | Bandwidth saturation, processing delays, potential Praos timing disruption | Stake (proportional magnitude) | Freshest-first delivery, traffic prioritization |

### Transaction-Based Denial of Service

Adversaries can degrade network performance and waste resources by submitting problematic transactions that consume processing capacity while providing minimal throughput value. These attacks exploit the transaction validation and mempool management overhead, forcing nodes to spend resources on transactions that either fail validation or conflict with each other. Unlike data withholding or protocol bursts, these attacks use normal transaction submission mechanisms, making them difficult to distinguish from legitimate network congestion.

The attack surface includes multiple vectors with varying resource requirements. Simple variants involve submitting duplicate, invalid, or conflicting transactions as regular client nodes. Network-level variants like mempool partitioning require control over network positioning to segment transaction propagation, creating inconsistent views across block producers.

An interesting economic variant involves honeypot contracts that entice many users to submit conflicting transactions by offering attractive rewards, using the ledger's intended functionality to generate artificial traffic. For example:
1. Lock a lot of ADA into a script that allows anyone to take `amount` while the remainder must be kept in the script.
2. Advertise the honey pot and that `amount` of ADA is available for free.
3. Race with everyone in claiming the output.
    a. If attacker is successful, only transaction fees were spent and `amount` can go back into the honey pot.
    b. Continue until funds run out.

Mempool partitioning differs from eclipse attacks on voting/diffusion in that it targets transactions flowing upstream rather than blocks propagating downstream: transactions propagate from clients to block producers, while block data flows from producers to voters and the broader network. This directional difference means that partitioning transaction pools requires different network positioning and currently lacks specific mitigation mechanisms.

**Impact**: These attacks primarily reduce effective transaction throughput while wasting computational and network resources. Invalid transactions consume validation cycles before being discarded. Conflicting transactions force nodes to process multiple alternatives when only one can succeed. Mempool partitioning can create scenarios where different block producers have inconsistent transaction views, potentially leading to conflicting EBs that don't reach quorum (in time) wasting voting resources. The honeypot variant creates artificial high-volume traffic that appears legitimate but provides low practical utility.

**Assets Affected**: High Throughput, Operational Sustainability

**Mitigation**: Transaction validation and fee mechanisms provide primary defense against invalid submissions. Pull-based transaction diffusion and strict mempool limits help contain resource consumption. Linear Leios' design prevents conflicting transactions from reaching permanent storage, limiting long-term impact. Additionally, endorsed transactions extend the mempool view through block diffusion, which is significantly harder to eclipse than upstream transaction propagation. However, mempool partitioning currently lacks specific countermeasures due to the directional nature of transaction flow. Detection of artificial transaction patterns is challenging since legitimate congestion can appear similar to attack traffic.

> [!NOTE]
> Linear Leios prevents conflicting transactions from reaching permanent storage, so impact is limited to temporary and mostly local resource waste. This is not the case for protocol variants with decoupled, concurrent block production (of EBs or IBs) where conflicting transactions would largely be "unpaid".

| #   | Method                                       | Effect                                     | Resources                              | Mitigation                                |
|-----|----------------------------------------------|--------------------------------------------|----------------------------------------|-------------------------------------------|
| T24 | Submit duplicate transactions                | Resource waste                             | Network bandwidth                      | Pull-based diffusion, validation          |
| T25 | Submit invalid transactions                  | Resource waste                             | Network bandwidth                      | Validation before propagation             |
| T26 | Submit conflicting transactions              | Processing waste, only one succeeds        | Transaction fees per conflict          | Linear Leios design                       |
| T27 | Mempool partitioning via network control     | Inconsistent mempools, conflicting EBs     | Network infrastructure control         | Limited: directional flow difference      |
| T28 | Honeypot contract creating transaction races | Artificial high-volume conflicting traffic | Contract deployment costs / incentives | Limited: attacker pays for some conflicts |

### System operation and Governance

**Description**: Threats arising from the complexity and scale of deploying and operating Leios, including governance failures, implementation inconsistencies, and resource sustainability challenges. These risks stem from the inherent complexity of coordinating protocol upgrades across a decentralized network and the long-term operational demands of increased system capacity.

Backward compatibility failures represent a particularly critical risk, as demonstrated by recent mainnet events (Nov 2025) where differences in node version behavior led to chain forks until stake consolidated on node versions with consistent behavior. Any functional change or complexity increase in Leios can create similar scenarios where subtle implementation differences cause honest nodes to diverge. Hard fork coordination attacks target the governance process itself, attempting to prevent or delay beneficial upgrades through manipulation of stakeholder voting or readiness signaling. While governance attacks primarily aim to prevent hard forks, they could theoretically create similar network inconsistency effects if they result in partial deployment scenarios where some nodes upgrade while others remain on older versions, effectively creating the same divergent behavior as implementation bugs.

Excessive chain growth poses a different challenge where the success of Leios could paradoxically threaten decentralization. If transaction throughput increases faster than SPO storage capabilities, honest stake could be forced offline due to resource constraints, inadvertently concentrating power among well-resourced operators and giving adversaries advantages in most stake-based attacks.

**Impact**: These threats can undermine the fundamental assumptions that keep Cardano secure and decentralized. Backward compatibility failures create chain splits that require manual coordination to resolve. Governance attacks can prevent beneficial upgrades entirely or create persistent network splits. Excessive growth can force honest operators offline, reducing effective honest stake and strengthening potential attackers' relative position in all stake-based attacks. Importantly, the network is most vulnerable during hard fork transition periods when mixed versions, uncertain governance outcomes, and coordination challenges create opportunities for adversaries to amplify other attack vectors from across the threat landscape.

**Assets Affected**: Blockchain Safety, Blockchain Liveness, Decentralization, Operational Sustainability

**Mitigation**: Extensive conformance testing and testnet deployments reduce implementation risks. Comprehensive communication, education, and staged rollouts help ensure successful governance coordination, including formal processes like Cardano Improvement Proposals (CIPs) and hard fork coordination meetings to build public discourse and increase acceptance. Conservative parameterization and monitoring of storage requirements protect against excessive growth, with protocol parameters adjusted based on observed SPO capabilities. The Ouroboros consensus protocols are provenly self-healing for temporary inconsistencies, but persistent issues require coordinated community response.

| #   | Method                                                   | Effect                                     | Resources                                    | Mitigation                                                   |
|-----|----------------------------------------------------------|--------------------------------------------|----------------------------------------------|--------------------------------------------------------------|
| T29 | Exploit implementation differences between node versions | Network fork, chain splits                 | Technical analysis, mixed-version targeting  | Comprehensive conformance testing, staged deployment         |
| T30 | Coordinate governance attacks to prevent hard fork       | Block beneficial upgrades, network splits  | Governance influence, infrastructure control | Communication, education, stakeholder coordination           |
| T31 | Honest demand exceeds SPO storage capabilities           | Forced node dropouts, reduced honest stake | Indirect through parameterization            | Conservative parameterization, load tests, staged deployment |
