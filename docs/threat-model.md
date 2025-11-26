---
Authors: Sebastian Nagel
Status: Draft
Version: 0.3
Last Updated: 2025-11-25
Next Review: 2026-01-30
---

# Leios Consensus Upgrade - Threat Model

A threat model for the Leios consensus change for Cardano. This reflects the simplified "Linear Leios" variant described in the CIP draft, which eliminates Input Blocks (IBs) and produces Endorser Blocks (EBs) alongside Ranking Blocks (RBs) by the same block producer.

See also [the threat model section in Leios Technical Report #1](./technical-report-1.md#threat-model) and more [comments on attack surface in Leios Technical Report #2](./technical-report-2.md#notes-on-the-leios-attack-surface).

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
**Description**: The fundamental guarantee that all honest nodes agree on the blockchain history and no conflicting valid chains exist.

**CIA Impact:**
- **Confidentiality**: Not applicable - blockchain is public
- **Integrity**: CRITICAL - Chain splits or conflicting histories would break consensus
- **Availability**: HIGH - Safety failures could halt the network indefinitely

**Leios-Specific Considerations**: Vote certificates and EB validation must not create conflicting blockchain states or enable double-spending.

### A2: Blockchain Liveness
**Description**: The guarantee that the blockchain continues to make progress by producing new blocks and processing transactions within reasonable time bounds.

**CIA Impact:**
- **Confidentiality**: Not applicable - blockchain is public
- **Integrity**: MEDIUM - Liveness failures don't corrupt existing data but prevent new valid transactions
- **Availability**: CRITICAL - Network becomes unusable if block production stops

**Leios-Specific Considerations**: EB creation, voting, and certificate inclusion must not prevent regular block production or create bottlenecks.

### A3: Transaction Validity, Availability, and Determinism
**Description**: All transactions included in the blockchain must be cryptographically valid, available to all network participants for verification, and deterministic (transactions only consume fees if successfully included, a key Cardano property).

**CIA Impact:**
- **Confidentiality**: Not applicable - transactions are public once included
- **Integrity**: CRITICAL - Invalid transactions would corrupt the ledger state; non-deterministic behavior would break fee guarantees
- **Availability**: HIGH - Unavailable transactions prevent proper validation and syncing

**Leios-Specific Considerations**: EBs reference transactions that must be available when the EB is processed; voting nodes must verify transaction availability before voting; deterministic behavior must be preserved across the EB endorsement and certification process.

### A4: Operational Sustainability
**Description**: Computational and network resources consumed by Stake Pool Operators to participate in the protocol, including CPU, memory, storage, and bandwidth. Resource increases are acceptable as long as they are covered by corresponding incentives to maintain operational sustainability.

**CIA Impact:**
- **Confidentiality**: LOW - Resource usage patterns could reveal some operational information
- **Integrity**: MEDIUM - Resource exhaustion could compromise node operation and validation
- **Availability**: HIGH - Excessive resource usage could force SPOs offline or prevent participation

**Leios-Specific Considerations**: New responsibilities (EB creation, voting, additional network protocols) must not significantly increase SPO operational costs relative to incentives or create barriers to participation.

### A5: Decentralization
**Description**: The distribution of block production, voting power, and network participation across many independent operators.

**CIA Impact:**
- **Confidentiality**: LOW - Centralization patterns are observable but don't directly affect data secrecy
- **Integrity**: HIGH - Centralization increases risk of coordinated attacks on consensus
- **Availability**: HIGH - Centralized infrastructure creates single points of failure

### A6: High Throughput
**Description**: The enhanced transaction processing capacity that Leios provides beyond basic Praos liveness, enabling the network to handle significantly more transactions per unit time.

**CIA Impact:**
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

| # | Method                             | Effect                                    | Resources                      | Mitigation            |
|---|------------------------------------|-------------------------------------------|--------------------------------|-----------------------|
| 1 | Any threat to Praos                | Leios is only as secure as Praos          | -                              | Dependency on Praos   |
| 2 | VRF grinding on EB eligibility     | Increased probability of EB creation      | CPU, stake (>20%)              | Ouroboros Phalanx R&D |
| 3 | VRF grinding on voting eligibility | Increased probability of voting selection | CPU, stake (>20%)              | Ouroboros Phalanx R&D |
| 4 | VRF key compromise                 | Unfair advantage in eligibility           | Very high cryptographic attack | Strong key management |

### Equivocation

In Leios, block producers and voters are only allowed one production per VRF lottery win for EBs and votes respectively. Equivocation occurs when malicious actors create multiple conflicting EBs or votes and diffuse them to different network segments, attempting to disrupt the protocol or gain unfair advantages. Equivocation detection mechanisms were already considered in the original Leios paper and are part of the protocol specification.

A particularly interesting case involves BLS key compromise for voting. When a BLS private key used for voting is compromised, legitimate key holders can intentionally equivocate (create conflicting votes) as a defensive measure until key rotation takes effect. This "defensive equivocation" invalidates both honest and adversarial votes signed by the compromised key, preventing the attacker from using the key maliciously while minimizing protocol disruption.

**Impact**: EB equivocation wastes network resources as nodes must process multiple conflicting blocks, only one of which can be valid. Vote equivocation can interfere with certificate creation and force nodes to choose between conflicting certificates. Double voting (voting on multiple conflicting EBs for the same voting period) can enable multiple certificates for conflicting transaction sets, wasting bandwidth and processing resources. However, the protocol's design limits the impact through equivocation detection and the principle that only RB inclusion affects chain selection, not certificate existence alone.

**Assets Affected**: Operational Sustainability, High Throughput

**Mitigation**: The Leios protocol specification includes explicit equivocation detection mechanisms that identify misbehaving nodes and equivocation proofs are forwarded through the network. For BLS key compromise, key rotation procedures enable recovery while defensive equivocation provides interim protection. Double voting has limited safety impact since multiple certificates can exist but only RB inclusion determines chain progression.

| # | Method             | Effect                                | Resources                    | Mitigation                               |
|---|--------------------|---------------------------------------|------------------------------|------------------------------------------|
| 5 | EB equivocation    | Lower throughput, resource waste      | Stake for block production   | Equivocation detection per Leios design  |
| 6 | Vote equivocation  | Interfere with certificate creation   | Stake for voting eligibility | Equivocation detection per Leios design  |
| 7 | Double voting      | Multiple certificates, resource waste | Stake for voting eligibility | Chain selection prioritizes RB inclusion |
| 8 | BLS key compromise | Unauthorized vote creation            | Cryptographic attack         | Key rotation, defensive equivocation     |

### Inaction and Nuisance

Producer nodes might attempt to disrupt the protocol by failing to play their assigned role or by creating invalid information. This includes declining to create EBs when entitled, declining to vote when eligible, or creating invalid EBs or votes. More serious variants involve certificate manipulation - including invalid certificates in RBs or attempting to cryptographically forge certificates without sufficient votes. The latter represents a fundamental attack on the protocol's cryptographic foundations and would indicate a severe compromise of the BLS signature scheme used for vote aggregation.

The incentive structure of Leios is designed such that most inaction attacks are self-defeating - nodes that decline to participate receive fewer rewards albeit very indirectly. Creating invalid blocks or votes wastes the attacker's own eligibility while create a minor annoyance to their first downstream nodes by burdening them with useless verification work, but the cryptographic aspects of Leios quickly catch and discard invalid submissions.

**Impact**: These attacks primarily reduce protocol throughput rather than compromising safety. Invalid submissions create computational overhead for validation but are quickly detected and discarded. The economic incentives generally discourage such behavior since attackers forfeit their own rewards while providing minimal disruption to the network.

**Assets Affected**: High Throughput, Operational Sustainability

**Mitigation**: The protocol's incentive structure provides the primary defense - participants who don't fulfill their roles receive proportionally reduced rewards. Cryptographic validation quickly identifies and discards invalid submissions to avoid assymetric resource attacks. The voting committee mechanism in Leios provides additional resilience by requiring multiple participants for EB certification, so individual node inaction has limited impact.

> [!WARNING]
>
> TODO: Move certificate forging somewhere else as it is quite different?

| #  | Method                               | Effect                            | Resources                    | Mitigation                               |
|----|--------------------------------------|-----------------------------------|------------------------------|------------------------------------------|
| 9  | Decline to create EB                 | Lower throughput                 | Stake for block production   | Reduced rewards                          |
| 10 | Decline to vote                      | Lower throughput                 | Stake for voting eligibility | Reduced rewards                          |
| 11 | Create invalid EB                    | Lower throughput, resource waste | Stake for block production   | Reduced rewards, validate before forward |
| 12 | Create invalid vote                  | Lower throughput, resource waste | Stake for voting eligibility | Reduced rewards, validate before forward |
| 13 | Reference invalid transactions in EB | Lower throughput, resource waste | Stake for block production   | Reduced rewards, validate before forward |
| 14 | Include invalid certificate in RB    | Lower throughput, resource waste | Stake for block production   | Certificate verification                 |
| 15 | Forge certificate without quorum     | Manipulate transaction inclusion  | Cryptographic attack         | Strong BLS cryptography                  |

### Omission and Manipulation

Block producers have control over which transactions to include in their EBs and can exploit this power for censorship (omission) or value extraction (manipulation). In Linear Leios, the coupled RB/EB production model gives every block producer opportunities to manipulate transaction ordering and selection within the EB they create alongside their RB.

This creates opportunities for front-running, where producers observe profitable transactions in the mempool and either reorder them for advantage or insert their own competing transactions. Censorship attacks involve deliberately omitting specific transactions to prevent their execution, though the mempool design limits effectiveness since omitted transactions will likely appear in subsequent honest blocks.

SPOs concerned about front-running competition may choose to bypass the EB mechanism entirely and include transactions directly in their RBs, avoiding exposure of these tranactions by the endorsement process. This reduces overall network throughput but provides some protection against MEV extraction by other producers. However, this strategy becomes self-limiting when transaction load exceeds Praos-only capacity, forcing delays upon these transactions and risking being front-run themselves.

**Impact**: These attacks primarily affect transaction fairness and market efficiency rather than protocol safety. Transaction reordering has limited impact on Cardano due to the EUTxO ledger design, where transactions either succeed or fail independently based on available UTxOs rather than global state changes. However, front-running and MEV extraction remain significant concerns - block producers can observe profitable transactions and may be able to compete with better prices or insert intermediary transactions - depending on application design. Censorship reduces liveness for targeted transactions but cannot permanently prevent inclusion due to the distributed nature of block production and the memory pool mechanism.

**Assets Affected**: Transaction Validity/Availability/Determinism, Decentralization

**Mitigation**: The primary defense is the memory pool design - omitted transactions remain available for inclusion in subsequent honest blocks, limiting censorship effectiveness. The distributed nature of block production means no single actor can permanently censor transactions. Detection of MEV extraction is challenging since legitimate transaction selection and ordering can appear similar to value extraction. Mitigation options are limited since EB opportunities are coupled to RB opportunities and cannot be parameterized separately.

| #  | Method                                      | Effect                                  | Resources                  | Mitigation                                                   |
|----|---------------------------------------------|-----------------------------------------|----------------------------|--------------------------------------------------------------|
| 16 | Omit transactions from EB                   | Lower throughput, temporary censorship | Stake for block production | Memory pool persistence                                      |
| 17 | Reorder transactions in EB                  | MEV, market manipulation                | Stake for block production | Limited detection capability                                 |
| 18 | Insert or replace transactions in EB        | MEV, market manipulation                | Stake for block production | Limited detection capability                                 |
| 19 | Ignore certificates, include txs in RB only | Lower throughput, avoid front-running  | Stake for block production | Reduced rewards, self-limiting when load exceeds RB capacity |

### Data withholding

> [!NOTE]
> This is also a [key threat informing the Leios technical design](./leios-design#data-withholding)

Adversaries deliberately prevent or delay the diffusion of EB transaction data to disrupt the certification process and degrade network throughput. This attack targets the fundamental dependency between transaction availability and EB certification, exploiting the gap between optimistic and worst-case diffusion scenarios that forms the basis of Leios' security argument. Unlike protocol bursts that overwhelm with volume, data withholding attacks manipulate timing and availability of critical data.

The attack operates by controlling when and to whom transaction data becomes available. When an EB is announced via an RB header, voting committee members must acquire and validate the complete transaction closure before casting votes. Adversaries can refuse to serve EB bodies, selectively withhold individual transactions, or strategically time data release to exceed voting deadlines. More sophisticated variants involve network-level manipulation to prevent data from reaching specific voting committee members within the required timeframe.

Advanced network-based variants can target high-stake voting nodes through eclipse attacks, where adversaries control the network connections of specific nodes to manipulate their information flow. Since voting committee membership involves some degree of public information, persistent voting members with significant stake could potentially be identified and targeted. However, eclipsing distinct nodes across a distributed network is non-trivial due to high network connectivity degrees and existing eclipse protection mechanisms.

A particularly dangerous and sophisticated variant targets blockchain safety itself by allowing EBs to achieve certification while preventing timely availability to all honest nodes. The adversary releases data to just enough voting committee members to achieve certification, but not to all network participants. This can create scenarios where certified EBs cannot be processed by honest nodes within the L_diff parameter, potentially violating Praos timing assumptions.

**Impact**: Data withholding primarily reduces throughput when EBs fail certification due to unavailable data, forcing wasted voting resources and delayed transaction processing. Thereotically, there is a high impact variant that can compromise blockchain safety by creating timing violations in Praos diffusion. By reducing the number of honest nodes that receive EB data in time for certification, adversaries also impair subsequent diffusion, making peer-to-peer propagation slower and less reliable. While occasional timing misses are normal in Ouroboros, persistent violations can lead to longer forks and degraded chain quality.

**Assets Affected**: High Throughput (primary), Blockchain Safety (sophisticated)

**Mitigation**: The L_diff parameter is designed to bound the gap between optimistic and worst-case diffusion even under adversarial conditions. The certification mechanism provides defense against stake-based withholding by requiring broad consensus before including EBs in the ledger. Network-level attacks require sophisticated countermeasures including redundant peer connections, timeouts for non-responsive nodes, and strategic committee selection. Eclipse protection mechanisms like "ledger peers", high network connectivity degrees, and connection diversity provide significant defense against targeted node isolation. Empirical validation of real-world network conditions against timing assumptions is essential.

> [!WARNING]
>
> TODO: Should this be also about network delays?

| #  | Method                                          | Effect                                             | Resources                              | Mitigation                                               |
|----|-------------------------------------------------|----------------------------------------------------|----------------------------------------|----------------------------------------------------------|
| 20 | Withhold announced EB or endorsed transactions  | Lower throughput                                   | Stake for block production             | Connection timeouts, peer pruning                        |
| 21 | Selectively withhold data from voting committee | Prevent honest EB certification, reduce throughput | Network position control               | Redundant peer connections, diffusion monitoring         |
| 22 | Selectively withhold data from honest nodes     | Allow certification, delay block propagation       | Network position control, modest stake | L_diff parameter sizing, worst-case diffusion validation |

### Protocol bursts

> [!NOTE]
> This is also a [key threat informing the Leios technical design](./leios-design#protocol-bursts)

Adversaries can withhold large numbers of EBs and their transaction closures over extended periods, then release them simultaneously to create concentrated bursts of network traffic. This attack exploits Leios' requirement that nodes must attempt to acquire any EB correctly announced even if it arrives too late for the node to vote on it, since the EB might still be certified by other nodes and required for future chain selection.

The attack magnitude depends on the adversary's stake proportion and EB size parameters, reaching hundreds of megabytes or even gigabytes of data to be fetched. An adversary controlling 1/3 stake could accumulate approximately 720 EBs over 12 hours, potentially totaling over 9 gigabytes if each EB contains maximum-sized transaction sets. When released simultaneously, this creates sustained bandwidth pressure that can degrade network performance even for nodes that validate only a small subset of the burst.

**Impact**: Protocol bursts target network resources and can escalate from operational issues to safety threats if traffic prioritization is insufficient. While the protocol requires Praos traffic to be prioritized over Leios traffic, imperfect prioritization during large bursts can delay Praos block diffusion beyond the critical timing parameter Δ, potentially compromising blockchain safety. The sheer bandwidth utilization is problematic even when honest nodes validate only a fraction of the burst data. Infrastructure limitations like cloud provider throttling, router buffer saturation, and asymmetric CPU/memory costs amplify the impact and make perfect prioritization challenging.

**Assets Affected**: Operational Sustainability, High Throughput, Blockchain Safety (if prioritization fails)

**Mitigation**: The primary defense is traffic prioritization implementing freshest-first delivery semantics - Praos traffic must be preferred over Leios traffic, and fresh Leios traffic over stale traffic. However, some infrastructural resources cannot be prioritized perfectly, including CPU, memory, disk bandwidth, and network router buffers. The attack's magnitude is bounded by the adversary's stake proportion, but ultimately requires engineering solutions for effective prioritization during burst conditions.

| #  | Method                                    | Effect                                                                     | Resources                      | Mitigation                                      |
|----|-------------------------------------------|----------------------------------------------------------------------------|--------------------------------|-------------------------------------------------|
| 23 | Withhold then release large number of EBs | Bandwidth saturation, processing delays, potential Praos timing disruption | Stake (proportional magnitude) | Freshest-first delivery, traffic prioritization |

### Legacy threats

> [!CAUTION]
>
> FIXME: Replace individual (example) threats with threat categories to be more exhaustive.

#### T1: Mempool Partitioning
**Description**: Attacker deliberately partitions the mempools of block producing nodes by submitting conflicting transactions (spending the same inputs) to different network segments, creating inconsistent views of valid transactions across the network.

**Prerequisites**:
- Control over multiple network positions to segment the peer-to-peer network
- Ability to create valid but conflicting transactions (same inputs, different outputs)
- Discovery of network topology and SPO peer relationships
- Timing coordination to submit conflicts before natural mempool synchronization

**Attack Vector**:
1. Attacker maps network topology and identifies cluster boundaries
2. Creates conflicting transaction pairs spending identical UTXOs
3. Submits Transaction A to Network Segment 1, Transaction B to Network Segment 2
4. Uses network position control (BGP, routing, eclipse techniques) to prevent cross-segment propagation
5. Slot/height battling SPOs from different segments create RBs endorsing different, conflicting transactions
6. Voting nodes must choose between conflicting EBs, potentially causing certification failures

**Cost**: HIGH - Requires significant network infrastructure, multiple nodes, and sustained coordination

**Likelihood**: LOW - Reduced attack surface due to coupled RB/EB production model, though possible when there are multiple eligible producers (slot / height battles).

**Impact**:
- **Throughput**: Different SPOs create conflicting EBs, causing vote splits and potential certification failures. This leads to throughput reduction when EBs fail certification, though system recovers in subsequent stages. This can occur both from deliberate mempool partitioning, but also naturally with "short forks" in the Praos chain where nodes select different chains.
- **Resources**: SPO's network bandwidth and compute resources wasted on processing, propagating, and voting on conflicting EBs that cannot all be certified
- **Trust**: Demonstrates network manipulation capability, though doesn't break core transaction guarantees

**Assets Affected**: High Throughput, Operational Sustainability

#### T2: Eclipse Attack on Voting Nodes
**Description**: Attacker isolates top voting nodes to manipulate vote collection by controlling their network connections and information flow.

**Prerequisites**:
- Control over significant network infrastructure (BGP routes, ISPs, or direct node connections)
- Knowledge of high-stake nodes' network addresses and topology
- Sustained resources to maintain isolation over multiple voting periods
- Timing coordination across multiple attack vectors

**Attack Vector**:
1. Identify network locations and peer connections of target voting nodes
2. Use BGP hijacking, DNS manipulation, or direct DoS to isolate nodes
3. Control information flow to isolated nodes (selective EB delivery)
4. Present different EBs to isolated vs. non-isolated voting nodes
5. Manipulate vote collection to either prevent certificates or enable invalid ones

**Cost**: VERY HIGH - Requires substantial network infrastructure control, ISP cooperation, or large-scale DDoS capabilities

**Impact**:
- **Vote Manipulation**: Limited impact due to quorum threshold - attacker needs to isolate significant voting stake
- **Throughput**: Reduction if enough voting nodes are offline, but system is resilient
- **Detectability**: Attack is highly visible through network monitoring and vote pattern analysis
- **Resource Cost**: High cost for attacker relative to limited impact on robust voting system

**Assets Affected**: Blockchain Safety, High Throughput

#### T3: Vote Flooding
**Description**: Malicious nodes flood the network with invalid or duplicate votes to overwhelm voting infrastructure and waste network resources.

**Prerequisites**:
- Access to network connectivity (minimal barrier)
- Knowledge of vote message format
- Basic understanding of voting protocol

**Attack Vector**:
1. Craft invalid votes (wrong signatures, non-existent EBs, duplicate votes)
2. Submit high volume of malicious votes through vote diffusion protocol
3. Target specific nodes or broadcast widely across network
4. Exploit any amplification in vote propagation mechanisms

**Cost**: VERY LOW - Requires minimal computational resources and network bandwidth

**Impact**:
- **Resource Consumption**: Forces legitimate nodes to process and validate spam votes
- **Network Congestion**: Increased bandwidth usage for vote diffusion protocol
- **Processing Overhead**: CPU cycles wasted on signature verification of invalid votes
- **Operational**: Potential degradation of node performance, but doesn't break consensus
- **Limited Scope**: Pull-based protocols provide natural rate limiting protection

**Assets Affected**: Operational Sustainability, High Throughput

#### T4: EB Withholding
**Description**: Eligible stake pools deliberately not announce or certify EBs when producing RBs they are entitled to create reducing network throughput.

**Prerequisites**:
- Stake pool eligibility for block production
- Economic incentive to withhold (e.g. censorship goals, reduced operational costs)

**Attack Vector**:
1. Win EB creation eligibility through normal VRF process, possibly enhanced by grinding
2. Create RB that does not announce an EB or don't include an already certified EB

**Cost**: LOW - No additional cost other than being a block producer, indirect opportunity cost of not included transaction fees

**Likelihood**: HIGH - Every block producer gets two opportunities to ignore EBs

**Impact**:
- **Throughput**: Reduced transaction processing capacity for this and next block opportunity. However, system may recover with next block production opportunity.
- **Resources**: Bandwidth and compute spent on voting wasted and needs to be redone.

**Assets Affected**: High Throughput

#### T5: Double Voting
**Description**: Nodes with delegated stake votes on multiple EBs that reference conflicting sets of transactions.

**Prerequisites**:
- Node is member on voting committee by stake
- Access to multiple conflicting EBs in the same voting period
- Malicious intent or compromised voting infrastructure

**Attack Vector**:
1. Receive or create multiple conflicting EBs for the same stage
2. Submit votes for multiple conflicting EBs instead of choosing one
3. Could enable multiple certificates for conflicting transaction sets
4. May coordinate with other compromised voting nodes

**Cost**: LOW-MEDIUM - Requires stake for voting eligibility, but double voting may be undetectable if EBs appear to be for different stages/pipelines

**Impact**:
- **Limited Effect**: Multiple certificates can exist but only RB inclusion affects chain selection
- **Resource Waste**: Additional bandwidth and processing for redundant certificates
- **No Safety Violation**: Chain safety depends on RB inclusion, not certificate existence
- **Detection Difficulty**: Voters may have plausible deniability if conflicting EBs aren't clearly marked as competing

**Assets Affected**: Operational Sustainability

#### T6: VRF Manipulation
**Description**: Attacker attempts to predict or manipulate EB eligibility by compromising the VRF (Verifiable Random Function) process.

**Prerequisites**:
- VRF private key compromise, or
- Cryptographic breakthrough against VRF security, or
- Implementation vulnerability in VRF generation/verification

**Attack Vector**:
1. Compromise VRF private keys through key extraction or side-channel attacks
2. Exploit implementation bugs in VRF computation
3. Use compromised keys to create favorable eligibility outcomes
4. Target specific slots or manipulate randomness to gain unfair advantage

**Cost**: VERY HIGH - Requires advanced cryptographic attacks or sophisticated key compromise

**Impact**:
- **Eligibility Bias**: Unfair advantage in EB creation opportunities
- **Centralization**: Could concentrate EB production in attacker's control
- **Cryptographic Failure**: Indicates fundamental security breach requiring protocol changes

**Assets Affected**: Blockchain Safety, Decentralization

#### T7: Stake Grinding
**Description**: Attacker manipulates stake distribution to influence voting power or EB eligibility through strategic delegation patterns.

**Prerequisites**:
- Significant economic resources to acquire or control stake
- Knowledge of stake distribution update timing (epoch boundaries)
- Ability to coordinate multiple delegation transactions

**Attack Vector**:
1. Accumulate stake through purchase or rental
2. Time delegation changes to maximize impact on upcoming epochs
3. Create multiple pools to spread influence while maintaining control
4. Coordinate with other actors to amplify manipulation effects

**Cost**: HIGH - Requires substantial capital investment in stake acquisition

**Impact**:
- **Voting Bias**: Disproportionate influence over EB certification
- **Eligibility Manipulation**: Increased EB creation opportunities
- **Centralization**: Concentration of power despite appearing decentralized

**Assets Affected**: Decentralization

#### T8: Transaction Withholding
**Description**: Attacker creates EBs referencing non-existing transactions to waste network resources and disrupt certification.

**Prerequisites**:
- Block production eligibility (RB + EB creation)
- Ability to generate valid, but non-existing transaction references

**Attack Vector**:
1. Win EB creation eligibility through normal VRF process, possibly enhanced by grinding
1. Create valid but non-existent transaction references
1. Create EB referencing these unavailable transactions and announce it in RB
1. Voting nodes cannot verify transaction availability, preventing certification

**Cost**: LOW - No additional cost other than being a block producer, indirect opportunity cost of not included transaction fees

**Likelihood**: MEDIUM - Requires block production eligibility but straightforward to execute

**Impact**:
- **Resource Waste**: Network bandwidth consumed attempting to fetch non-existent transactions
- **Throughput**: Temporary reduction when EBs fail certification due to unavailable transactions
- **Operational**: SPO resources wasted on failed validation and fetching attempts

**Assets Affected**: High Throughput, Operational Sustainability

#### T9: Front-Running
**Description**: Block producers observe profitable transactions and reorder or insert their own transactions to extract value before the original transaction executes.

**Prerequisites**:
- Block production eligibility (RB + EB creation)
- MEV (Maximal Extractable Value) opportunities in transaction sets
- Knowledge of transaction dependencies and profitable patterns

**Attack Vector**:
1. Monitor mempool for profitable transaction patterns
2. Create front-running transactions
3. Replace target transactions with front-running transactions in EB
4. Extract value through arbitrage, sandwich attacks, or liquidations

**Cost**: LOW - Opportunity cost only, since already producing the block

**Likelihood**: MEDIUM-HIGH - Every RB producer gets EB opportunity with larger transaction capacity, creating more MEV opportunities, especially with lucky leader schedules

**Impact**:
- **Value Extraction**: Users receive worse execution prices
- **Market Inefficiency**: Creates unfair advantages for block producers
- **Increased Opportunity**: Larger EBs and frequent production create more MEV extraction opportunities (than with Praos already)
- **Detectable**: Transaction patterns can reveal front-running behavior

**Assets Affected**: Transaction Validity/Availability/Determinism, Decentralization

#### T10: Hard Fork Coordination Attack
**Description**: Disruption during the hard fork transition period to split the network, cause instability, or prevent the hard fork from succeeding.

**Prerequisites**:
- Knowledge of hard fork activation timeline and governance process
- Control over significant network infrastructure or stake
- Influence over SPOs, dReps, or governance participants
- Coordination capabilities during transition window

**Attack Vector**:
1. **Governance Manipulation**: Influence SPOs and dReps to vote against or delay governance actions
2. **Readiness Signaling Attack**: Manipulate hard fork readiness signals to create false coordination
3. **Transition Timing**: Coordinate attacks precisely during hard fork activation
4. **Version Confusion**: Exploit incompatibilities between old/new nodes
5. **Infrastructure Targeting**: Attack critical infrastructure during vulnerable transition period

**Cost**: HIGH - Requires significant coordination, infrastructure control, or governance influence

**Impact**:
- **Hard Fork Prevention**: Could block beneficial protocol upgrades entirely
- **Network Split**: Persistent chain splits if coordination fails
- **Governance Disruption**: Undermines democratic upgrade process
- **Infrastructure Damage**: Critical period where network is most vulnerable
- **Recovery Complexity**: Requires coordinated response and potential manual intervention

**Assets Affected**: Blockchain Safety, Blockchain Liveness, High Throughput

#### T11: Backward Compatibility Exploitation
**Description**: Attacker exploits differences between old and new node behavior during transition period.

**Prerequisites**:
- Understanding of protocol differences between versions
- Access to both old and new node implementations
- Ability to craft messages that behave differently across versions

**Attack Vector**:
1. Identify behavioral differences between node versions
2. Craft messages/transactions that exploit these differences
3. Target mixed-version network segments
4. Cause inconsistent processing or validation failures

**Cost**: MEDIUM - Requires technical analysis but minimal infrastructure

**Impact**:
- **Inconsistency**: Different node versions may reach different conclusions
- **Resource Waste**: Nodes spend resources on incompatible processing
- **Operational**: May force emergency patches or version rollbacks

**Assets Affected**: Operational Sustainability, High Throughput

#### T12: Honey Pot Contract

**Description**: An attacker deliberately makes ADA available on-chain so anyone races to claim it with the goal of producing many conflicting transactions. This is very similar to T1, but uses cryptocurrency instead of network resources.

**Prerequisites**:
- Knowledge of building a Cardano smart contract
- Enough ADA to appeal to enough users

**Attack Vector**:
1. Lock a lot of ADA into a script that allows anyone to take `amount` while the remainder must be kept in the script.
2. Advertise the honey pot and that `amount` of ADA is available for free.
3. Race with everyone in claiming the output.
    a. If attacker is successful, only transaction fees were spent and `amount` can go back into the honey pot.
4. Continue until funds run out.

**Cost**: HIGH - Enough ADA to appeal many concurrent users and keep the attack going.

**Impact**:
- **Resource Waste**: Network processes all conflicting transactions trying to spend the honey pot output, but only one pays fees at a time. Highest costs are from perpetual storage when conflicting transactions are submitted concurrently.
- **Throughput**: Reduces available throughput by amount of transactions attracted by the honey pot.
- **Artificial traffic / low tps**: While this artificial traffic will account into the systems throughput, typically measured in transactions per second (tps), the attacker could require these transactions to be big and computationally costly, resulting in a relatively low tps addition.

**Assets Affected**: High Throughput, Operational Sustainability

#### T13: Delayed Praos Blocks

> [!WARN]
> Is this a threat or rather part of the Blockchain Safety asset?

**Description**: Delaying Praos blocks due to long ledger state building (too many txs), impacting liveness and safety.

**Impact**:
- **Chain Quality**: Increased likelihood of chain forks and lower chain quality

**Assets Affected**: Blockchain Safety

#### T14: Excessive Chain Growth

> [!WARN]
> TODO and how do we describe threats that are not attacks?

**Description**: Chain growing too much due to honest demand and too high capacity parameterization (as a threat, not an attack). When SPOs cannot add as much storage as is needed, they cannot validate the chain and decentralization is impacted.

**Assets Affected**: Operational Sustainability, Decentralization


## Mitigation Strategies

#### M1: Mempool Partitioning Defense
**Addressing threats**: T1

**Decision**: MITIGATE + ACCEPT

**Control type**: Preventive + Detective

**Implementation**:
- Redundant downstream peer connections and selection similar to downstream
- Peer connection churn for nodes serving non-chain transactions repeatedly
- Fair transaction diffusion across peer connections
- Strict limits on perpetual storage (no conflicting tx storage)
- Network topology monitoring for partition detection

**Validation**: Simulation testing with network partitions

**Cost**: MEDIUM - Protocol changes and monitoring infrastructure

**Accepted Impact**: Temporary throughput reduction and resource waste from conflicting transactions, as long as perpetual storage costs are contained

#### M2: Eclipse Attack Prevention
**Addressing threats**: T2

**Decision**: MITIGATE

**Control type**: Preventive + Detective

**Implementation**:
- Redundant and tiered upstream peer connections
- Detect and punish censoring across mini protocols
- Apply protection to all critical path network protocols (vote diffusion, EB diffusion, block fetch)
- Network monitoring and anomaly detection

**Validation**: Penetration testing and network analysis

**Cost**: MEDIUM - Monitoring infrastructure and operational procedures

#### M3: Vote Flooding Protection
**Addressing threats**: T3

**Decision**: MITIGATE

**Control type**: Preventive

**Implementation**:
- Rate limiting on vote acceptance per node
- Vote signature validation before propagation
- Pull-based protocol design (already implemented)
- Resource quotas for vote processing

**Validation**: Load testing with malicious vote patterns

**Cost**: LOW - Protocol design already provides protection

#### M4: Transaction Availability Enforcement
**Decision**: MITIGATE

**Control type**: Preventive + Corrective

**Implementation**:
- Protocol violation when peer serving EB cannot provide endorsed transactions
- Mandatory transaction fetch attempt from EB-serving peer
- Connection pruning with back-off for timeout violations
- Multi-peer transaction sourcing as fallback

**Validation**: Testing with unavailable transaction scenarios and peer timeouts

**Cost**: LOW - Protocol enforcement mechanism

**Addressing threats**: T8

#### M5: Over-Parameterization

> [!CAUTION]
> This is not available anymore with Linear Leios.

**Addressing threats**: T4, T8, T9

**Decision**: MITIGATE

**Control type**: Preventive

**Implementation**:
- Parameterize EB opportunities and sizes for adversarial stake assumptions
- Example: Assume 30% adversarial stake, produce 2 EBs per stage on average
- Size EBs 15% larger to compensate for potential withholding or front-running
- Bound throughput loss to guaranteed capacity levels

**Validation**: Game-theoretic analysis and simulation with various adversarial stake percentages

**Cost**: LOW - Protocol parameterization only

#### M6: Double Voting Response
**Addressing threats**: T5

**Decision**: ACCEPT

**Control type**: None

**Implementation**: None required

**Validation**: Not applicable

**Cost**: None

**Accepted Impact**: Multiple certificates may exist but only RB inclusion affects chain selection, so no safety impact

#### M7: VRF and Stake Manipulation Response
**Addressing threats**: T6, T7

**Decision**: ACCEPT

**Control type**: None

**Implementation**: None required

**Validation**: Not applicable

**Cost**: None

**Accepted Impact**: Prerequisites too high (cryptographic breakthrough or massive capital) and likelihood too low to justify mitigation effort

#### M8: Front-Running Monitoring
**Addressing threats**: T9

**Decision**: ACCEPT

**Control type**: Detective

**Implementation**:
- Monitor transaction ordering patterns in EBs and RBs
- Detect suspicious value extraction behaviors
- Automated alerts for front-running patterns
- Public reporting of detected MEV activity

**Validation**: Pattern analysis on historical transaction data

**Cost**: MEDIUM - Monitoring and analysis infrastructure

**Accepted Impact**:
  - Front-running will occur but detection helps maintain transparency and potential future governance responses
  - Cannot mitigate because EB opportunities are tied to RB opportunities and cannot be parameterized separately

#### M9: Hard Fork Coordination Protection
**Addressing threats**: T10

**Decision**: MITIGATE

**Control type**: Preventive

**Implementation**:
- Up-front communication, education and transparency throughout development
- Cardano Improvement Proposal (CIP) publication
- Public demonstrations and devnets
- Staged rollout through testnets prior to hard-fork
- Monitor adoption and readiness via collaboration with key component maintainers
- Hard fork coordination meetings via Intersect Technical Steering Committee (TSC)

**Validation**: Stakeholder surveys, adoption metrics, testnet participation rates

**Cost**: MEDIUM - Extensive coordination and communication effort

#### M10: Backward Compatibility Protection
**Addressing threats**: T11

**Decision**: AVOID + MITIGATE

**Control type**: Preventive

**Implementation**:
- Avoid breaking changes in protocol design where possible
- Comprehensive testing of old/new node behavior interactions
- Automated compatibility test suites
- Mixed-version network testing on testnets

**Validation**: Integration testing with various client versions and protocol combinations

**Cost**: MEDIUM - Testing infrastructure and compatibility analysis

### M11: No Conflicting Transactions
**Addressing threats**: T1, T12

**Decision**: MITIGATE

**Control type**: By design

**Implementation**:
- Protocol design inherently prevents conflicting transactions from reaching the chain
- No permanent storage of conflicting transactions unlike concurrent variants
- Ledger detects conflicts within an EB before voting
- Endorsed transactions are used to update the mempool view
- Data diffusion limits the number of conflicting transactions and does not amplify deliberately conflicting transaction propagation

**Validation**: Ensure mempool and data diffusion behavior; integration tests using conflicting transactions confirm bounded load on network and compute

**Cost**: NONE - Built into protocol design

## Review and Maintenance

This threat model should be reviewed and updated:
- Before each major protocol upgrade
- After any security incidents
- Quarterly during active development
- When new attack vectors are discovered
