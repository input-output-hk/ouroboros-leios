---
Authors: Sebastian Nagel
Document Version: 1.0
Last Updated: 2025-07-10
Next Review: 2025-09-10
---
# Leios Consensus Upgrade - Threat Model

A threat model for the Leios consensus change for Cardano. This was created by roughly following the [OWASP threat modeling process](https://owasp.org/www-community/Threat_Modeling_Process).

See also [the threat model section in Leios Technical Report #1](./technical-report-1.md#threat-model) and more [comments on attack surface in Leios Technical Report #2](./technical-report-2.md#notes-on-the-leios-attack-surface).

## System Overview

> [!NOTE]
> The described system here is the heavily simplified EB-only variant of Leios. Whenever we update this, reflect on existing assets, threats and mitigations, as well as add new ones accordingly.

### Description
Leios is an overlay protocol on top of Ouroboros Praos that enhances transaction throughput by introducing Endorser Blocks (EBs) alongside regular Praos blocks (Ranking Blocks - RBs). The system maintains backward compatibility at the client interface while introducing new responsibilities for stake pools.

### Key Components

#### Entities
- **Mempool**: List of valid, pending transactions that could be added to the chain. Limited in size
- **Ranking Block (RB)**: Standard Praos block enhanced with a Leios certificate. Limited in size
- **Endorser Block (EB)**: New block type that references transactions for inclusion. May be substantially bigger than Praos blocks (currently on mainnet ~88 kB) with sizes around ~640 kB for 20k transaction references
- **Leios Certificate**: Cryptographic proof about aggregated stake-weighted votes on EB validity and transaction availability
- **EB Lottery**: Separate (to Praos) VRF lottery for EB creation rights

#### Network Protocols
- **Transaction Submission Protocol**: Existing protocol to announce and fetch transactions, served upstream
- **Chain Sync Protocol**: Existing protocol for tracking block headers of currently selected chain, served downstream
- **Block Fetch Protocol**: Existing protocol for downloading blocks, served downstream
- **EB Announcement Protocol**: New protocol to gossip EB existence, served downstream
- **EB Fetch Protocol**: New protocol for retrieving EBs, served downstream
- **Transaction Fetch Protocol**: New protocol for retrieving endorsed transactions, served downstream
- **Vote Diffusion Protocol**: New protocol for propagating votes on EBs, served downstream

#### Roles
- **Block Producers**: Produce blocks, now enhanced with EB creation and voting responsibilities
- **Relays**: Participate in transaction and block diffusion
- **Clients**: Submit transactions and observe the chain / ledger state evolving, ideally maintain backward compatibility and may largely unaware of Leios mechanics

#### System Flow
1. Clients submit transactions, which get added to the mempool and diffuse through the Cardano network
1. Stake pools create EBs based on VRF eligibility (parameterizable stage length)
1. EBs are announced and propagated through the network
1. A committee of nodes (> 500 by stake) vote on EB validity and transaction availability
1. If a quorum of voting stake (> 60%) approves, a certificate is created
1. Certificates are included in the next available RB (every ~20 seconds)
1. Missing transactions are fetched on-demand when EBs are processed

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

### A5: Decentralization Properties
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

Notable threats to the system that could impact assets.

### Network-Level Threats

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
5. SPOs in different segments create EBs endorsing different conflicting transactions
6. Voting nodes must choose between conflicting EBs, potentially causing certification failures

**Cost**: MEDIUM-HIGH - Requires significant network infrastructure, multiple nodes, and sustained coordination

**Impact**:
- **Throughput**: Different SPOs create conflicting EBs, causing vote splits and potential certification failures. This leads to throughput reduction when EBs fail certification, though system recovers in subsequent stages
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

#### T3: Vote Flooding Attack
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

### Consensus-Level Threats

#### T4: EB Withholding Attack
**Description**: Eligible stake pools deliberately withhold EBs they are entitled to create, reducing network throughput and potentially enabling censorship.

**Prerequisites**:
- Stake pool eligibility for EB creation (via VRF lottery)
- Economic incentive to withhold (e.g., competing EB producers, censorship goals)

**Attack Vector**:
1. Win EB creation eligibility through normal VRF process or possibly enhanced by grinding
2. Either create EB but not propagate it, or simply abstain from creation
3. May selectively withhold EBs containing specific transactions (censorship)
4. Could coordinate with other eligible pools to maximize impact

**Cost**: LOW - Opportunity cost of foregone rewards from EB creation

**Impact**:
- **Throughput**: Reduced transaction processing capacity when EBs are withheld
- **Censorship**: Potential to delay specific transactions if coordinated
- **Temporary**: System recovers with next EB opportunity or alternative producers
- **Limited**: Cannot permanently block transactions due to multiple eligibility opportunities

**Assets Affected**: High Throughput, Decentralization Properties

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

**Assets Affected**: Blockchain Safety, Decentralization Properties

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

**Assets Affected**: Decentralization Properties

### Transaction-Level Threats

#### T8: Transaction Availability Attack
**Description**: Attacker creates EBs referencing unavailable transactions to waste network resources and disrupt certification.

**Prerequisites**:
- EB creation eligibility (via VRF)
- Control over transaction propagation to specific network segments
- Coordination between transaction submission and EB creation

**Attack Vector**:
1. Submit transactions to limited network segments
2. Create EB referencing these transactions before full propagation
3. Voting nodes cannot verify transaction availability, preventing certification
4. Forces futile transaction fetching attempts across network

**Cost**: LOW - Minimal beyond normal EB creation costs

**Impact**:
- **Resource Waste**: Network bandwidth consumed fetching unavailable transactions
- **Throughput**: Temporary reduction when EBs fail certification
- **Operational**: SPO resources wasted on failed validation attempts

**Assets Affected**: High Throughput, Operational Sustainability

#### T9: Transaction Front-Running
**Description**: EB producers observe profitable transactions and reorder or insert their own transactions to extract value before the original transaction executes.

**Prerequisites**:
- EB creation eligibility
- MEV (Maximal Extractable Value) opportunities in transaction sets
- Knowledge of transaction dependencies and profitable patterns

**Attack Vector**:
1. Monitor mempool for profitable transaction patterns
2. Create competing or parasitic transactions
3. Include both in EB with favorable ordering for attacker
4. Extract value through arbitrage, sandwich attacks, or liquidations

**Cost**: LOW - Opportunity cost only, plus normal EB creation requirements

**Impact**:
- **Value Extraction**: Users receive worse execution prices
- **Market Inefficiency**: Creates unfair advantages for EB producers
- **Detectable**: Transaction patterns can reveal front-running behavior
- **Existing Issue**: Already present with RB producers, Leios increases frequency

**Assets Affected**: Transaction Validity/Availability/Determinism, Decentralization Properties

### Deployment-Level Threats

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

## Risk Assessment Matrix

| Threat                        | Impact | Likelihood | Risk Level | Priority |
|-------------------------------|--------|------------|------------|----------|
| T1: Mempool Partitioning      | HIGH   | MEDIUM     | HIGH       | P1       |
| T2: Eclipse Attack            | HIGH   | MEDIUM     | HIGH       | P1       |
| T8: Transaction Availability  | HIGH   | MEDIUM     | HIGH       | P1       |
| T10: Hard Fork Coordination   | HIGH   | MEDIUM     | HIGH       | P1       |
| T3: Vote Flooding             | MEDIUM | HIGH       | MEDIUM     | P2       |
| T5: Double Voting             | LOW    | LOW        | LOW        | P4       |
| T6: VRF Manipulation          | HIGH   | LOW        | MEDIUM     | P2       |
| T4: EB Withholding            | MEDIUM | MEDIUM     | MEDIUM     | P3       |
| T9: Transaction Front-Running | MEDIUM | MEDIUM     | MEDIUM     | P3       |
| T11: Backward Compatibility   | MEDIUM | MEDIUM     | MEDIUM     | P3       |
| T7: Stake Grinding            | MEDIUM | LOW        | LOW        | P4       |

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

**Cost**: Medium - Protocol changes and monitoring infrastructure

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

**Cost**: Medium - Monitoring infrastructure and operational procedures

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

**Cost**: Low - Protocol design already provides protection

#### M4: Transaction Availability Enforcement
**Decision**: MITIGATE

**Control type**: Preventive + Corrective

**Implementation**:
- Protocol violation when peer serving EB cannot provide endorsed transactions
- Mandatory transaction fetch attempt from EB-serving peer
- Connection pruning with back-off for timeout violations
- Multi-peer transaction sourcing as fallback

**Validation**: Testing with unavailable transaction scenarios and peer timeouts

**Cost**: Low - Protocol enforcement mechanism

**Addressing threats**: T8

#### M5: Over-Parameterization
**Addressing threats**: T4, T8

**Decision**: MITIGATE

**Control type**: Preventive

**Implementation**:
- Parameterize EB opportunities and sizes for adversarial stake assumptions
- Example: Assume 30% adversarial stake, produce 2 EBs per stage on average
- Size EBs 15% larger to compensate for potential withholding
- Bound throughput loss to guaranteed capacity levels

**Validation**: Game-theoretic analysis and simulation with various adversarial stake percentages

**Cost**: Low - Protocol parameterization only

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

#### M8: Front-Running Response
**Addressing threats**: T9

**Decision**: ACCEPT + MITIGATE

**Control type**: Detective

**Implementation**:
- Monitor transaction ordering patterns in EBs and RBs
- Detect suspicious value extraction behaviors
- Automated alerts for front-running patterns
- Public reporting of detected MEV activity

**Validation**: Pattern analysis on historical transaction data

**Cost**: Low - Monitoring and analysis infrastructure

**Accepted Impact**: Front-running will occur but detection helps maintain transparency and potential future governance responses

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

**Cost**: Medium - Extensive coordination and communication effort

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

**Cost**: Medium - Testing infrastructure and compatibility analysis

## Review and Maintenance

This threat model should be reviewed and updated:
- Before each major protocol upgrade
- After any security incidents
- Quarterly during active development
- When new attack vectors are discovered
