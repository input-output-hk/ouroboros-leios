---
Title: Leios Technical Design and Implementation Plan
Status: Draft
Version: 0.1
Authors:
  - Sebastian Nagel <sebastian.nagel@iohk.io>
---

# Leios Technical Design and Implementation Plan

## Document Purpose and Scope

This document provides detailed technical specifications, architectural designs, and implementation strategies for integrating Leios into cardano-node. While the Impact Analysis document identifies *what* needs to change and *why*, this Technical Design document specifies *how* to implement those changes, with sufficient detail for engineering teams to execute the work.

**Audience**: Developers and system architects working on Leios implementations.

**Related Documents**:
- [Leios Impact Analysis](./ImpactAnalysis.md) (requirements and high-level changes)
- [CIP-0164](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md) (protocol specification)
- Component-specific design documents (as referenced)

---

# 1. Architectural Overview

## 1.1 System Context
- High-level architecture showing `cardano-node` in the broader Cardano ecosystem
- Key external systems and interfaces
- Data flows between major subsystems

## 1.2 Container Diagram (C4 Model)
**[CENTRAL ARTIFACT]** - Detailed C4 container diagram showing:
- **New containers**: LeiosEbStore, LeiosVoteStorage, LeiosTxCache
- **Updated containers**: BlockProduction, ChainDB, LedgerDB, Mempool, Network protocols
- **Unchanged containers**: (grayed out for context)
- **Interactions**: Message flows, data flows, dependencies
- **Annotations**: Key responsibilities, capacity/performance targets

### Diagram Views
- **Diff view**: Highlighting what's new vs. updated vs. unchanged
- **Data flow view**: Transaction and block lifecycle through the system
- **Voting flow view**: Vote production, aggregation, and certificate generation
- **Storage view**: How different block types and votes are persisted

## 1.3 Component Relationships
- Dependency graph between components
- Interface contracts and APIs
- Shared data structures
- Concurrency model and thread interaction

---

# 2. Detailed Component Designs

For each major component impacted by Leios, provide:

## 2.1 Consensus Layer

### 2.1.1 Block Production Thread (UPD-LeiosAwareBlockProductionThread)
**Responsibilities**:
- Generate EB alongside RB
- Decide between TxRB and CertRB
- Coordinate with Mempool for transaction selection

**Design Decisions**:
- Why single thread vs. separate threads?
- EB generation timing and sequencing
- Transaction selection algorithm for EBs

**Detailed Specification**:
- State machine diagram
- Pseudocode for main loop
- Error handling and edge cases
- Performance targets (latency, throughput)

**Interfaces**:
- Input: Mempool state, ChainDB tip, vote storage
- Output: RB, EB, updates to storage layers

**Testing Strategy**:
- Unit tests for EB/RB generation logic
- Integration tests with Mempool
- Property-based tests for invariants

### 2.1.2 Vote Production Thread (NEW-LeiosVoteProductionThread)
**Responsibilities**:
- Detect newly available EB closures
- Validate EBs according to voting rules
- Issue votes when rules are satisfied

**Design Decisions**:
- Event-driven vs. polling approach
- Validation priority when multiple EBs arrive
- Handling race conditions with chain selection changes

**Detailed Specification**:
- Triggering conditions and event sources
- Validation procedure flowchart
- Vote signing and formatting
- Timeout and retry logic

**Interfaces**:
- Input: EB closures from LeiosEbStore, ChainDB selection
- Output: Signed votes to LeiosVoteStorage and Network layer

**Concurrency**:
- Thread safety guarantees
- Lock ordering and deadlock prevention
- Interaction with other consensus threads

**Testing Strategy**:
- Simulation of EB arrival patterns
- Validation correctness tests
- Timing and race condition tests

### 2.1.3 Vote Storage (NEW-LeiosVoteStorage)
**Responsibilities**:
- Store votes indexed by RB
- Aggregate votes and detect certificate threshold
- Evict old votes based on age

**Design Decisions**:
- In-memory data structure choice (HashMap, btree, etc.)
- Age-based eviction policy parameters
- Certificate generation trigger mechanism

**Detailed Specification**:
- Data structures and algorithms
- Memory bounds and capacity planning
- Eviction algorithm (conservative age threshold)
- Thread-safe access patterns

**Performance Requirements**:
- Vote insertion latency: <1ms
- Vote lookup latency: <1ms
- Memory overhead: O(votes in last ~10 minutes)
- Certificate detection latency: <10ms after threshold

**Testing Strategy**:
- Load tests with adversarial vote patterns
- Memory profiling under ATK-LeiosProtocolBurst
- Correctness of certificate detection
- Eviction policy validation

### 2.1.4 EB Storage (NEW-LeiosEbStore)
**Responsibilities**:
- Persist EB closures to disk
- Manage volatile and immutable dichotomy
- Provide fast retrieval for validation and application

**Design Decisions**:
- Disk storage format (key-value, append-only, etc.)
- Volatile to immutable promotion criteria
- Index structure for lookups

**Detailed Specification**:
- File format and serialization
- Directory structure and naming conventions
- Garbage collection / pruning strategy
- Recovery and crash consistency

**Performance Requirements**:
- Write throughput: sustain ATK-LeiosProtocolBurst (>1GB)
- Read latency: <50ms for EB closure retrieval
- Disk space: manage up to 36 hours of volatile EBs

**Integration Points**:
- ChainDB for certified EB promotion
- LedgerDB for EB application
- BlockFetch for EB diffusion

**Testing Strategy**:
- Crash recovery tests
- Disk space management tests
- Performance benchmarks under burst scenarios
- Integration tests with ChainDB

### 2.1.5 Transaction Cache (NEW-LeiosTxCache)
**Responsibilities**:
- Cache transactions from EBs and Mempool
- LRU eviction based on age (~1 hour)
- Provide fast lookup by transaction hash

**Design Decisions**:
- Why separate from Mempool?
- In-memory vs. memory-mapped file
- Priority queue implementation for age tracking

**Detailed Specification**:
- Data structures: priority queues (index and age)
- ByteArray management to minimize GC pressure
- Double-buffered mmap file details
- Lock-free or locked access patterns

**Capacity Planning**:
- Expected: ~180 slots * full EB capacity
- Adversarial: up to 131,000 transactions per hour
- Index size and memory overhead analysis

**Performance Requirements**:
- Insertion: <100μs per transaction
- Lookup: <100μs per transaction
- GC allocation rate: minimal (manual memory management)

**Testing Strategy**:
- Memory profiling under load
- Cache hit rate analysis
- Eviction correctness tests
- Concurrency and thread-safety tests

### 2.1.6 CertRB Staging Area (NEW-LeiosCertRbStagingArea)
**Responsibilities**:
- Buffer CertRBs until their EB closures arrive
- Trigger ChainSel when closure becomes available

**Design Decisions**:
- Simple buffer vs. VolDB index-aware approach
- Whether to validate certificates before closure arrives

**Detailed Specification**:
- Data structure for buffering
- Notification mechanism for closure arrival
- Timeout and error handling for missing closures

**Alternative Designs**:
- Pros/cons of VolDB path-finding awareness
- Trade-offs with re-triggering ChainSel

**Testing Strategy**:
- Test CertRB arrival before/after closure
- Verify ChainSel behavior
- Edge cases with deep forks

### 2.1.7 LedgerDB Updates (UPD-LeiosLedgerDb)
**Responsibilities**:
- Retrieve EB closures when applying CertRBs
- Apply transactions without full validation (third validation level)

**Design Decisions**:
- Whether to cache EB ledger states
- Thunking EB reapplication vs. immediate

**Detailed Specification**:
- Interface changes to ledger application
- Error handling for missing closures
- Rollback and fork handling

**Testing Strategy**:
- Integration tests with LeiosEbStore
- Chain switch scenarios
- Correctness of third validation level

### 2.1.8 Mempool Capacity Update (UPD-LeiosBiggerMempool)
**Responsibilities**:
- Hold sufficient transactions for full EB + full RB

**Design Decisions**:
- New capacity: 2x EB capacity minimum
- Eviction policy adjustments

**Detailed Specification**:
- Configuration parameters
- Memory allocation and monitoring
- Interaction with block production

**Testing Strategy**:
- Load tests with full capacity
- Eviction behavior under stress

### 2.1.9 BlockFetch Client Updates (UPD-LeiosRbBlockFetchClient)
**Responsibilities**:
- Route CertRBs through staging area when needed
- Fetch EB closures alongside RBs

**Design Decisions**:
- Prefetching strategy for EB closures
- Priority of EB vs. RB fetches

**Detailed Specification**:
- Modified block fetch logic
- Interaction with staging area
- Error handling for incomplete closures

**Testing Strategy**:
- Diffusion simulation tests
- Network delay scenarios
- Verification of L_diff benefits

---

## 2.2 Network Layer

### 2.2.1 Leios Mini-Protocols (NEW-LeiosMiniProtocols)
**Responsibilities**:
- Diffuse EB announcements, EB bodies, EB transactions, votes

**Protocol Specifications**:
- Message types and formats (CDDL schemas)
- State machines for client and server
- Flow control and backpressure mechanisms

**Design Decisions**:
- Separate mini-protocols vs. combined
- Request/reply separation for FFD support
- Notification mechanism design

**Detailed Specification**:
- Message sequence diagrams
- Protocol versioning and negotiation
- Error conditions and recovery
- Timeouts and retry logic

**Performance Requirements**:
- Support burst of >1GB download
- Minimize latency for young EBs
- Efficient handling of many peers

**Testing Strategy**:
- Protocol conformance tests
- Adversarial peer behavior tests
- Network partition and delay tests
- Throughput and latency benchmarks

### 2.2.2 Fetch Decision Logic (NEW-LeiosFetchDecisionLogic)
**Responsibilities**:
- Decide which EBs/votes to fetch from which peers
- Prioritize fresh over stale content
- Avoid redundant fetches

**Design Decisions**:
- Heuristics for prioritization
- Peer selection strategy
- Deduplication logic

**Detailed Specification**:
- Decision algorithm pseudocode
- Scoring function for fetch candidates
- State tracking per peer

**Testing Strategy**:
- Simulation of various network topologies
- Verification of FFD (freshest-first delivery)
- Efficiency metrics (redundant fetches, time to acquire)

### 2.2.3 Multiplexer Bias (NEW-LeiosPraosMuxBias)
**Responsibilities**:
- Prioritize Praos mini-protocols over Leios

**Design Decisions**:
- Degree of bias (strong vs. full preference)
- Impact on fairness and starvation

**Detailed Specification**:
- Scheduling algorithm modification
- Queue management
- Starvation prevention for Leios

**Performance Requirements**:
- Negligible impact on Praos diffusion
- Measurable impact on Praos vs. Leios under contention

**Testing Strategy**:
- Benchmark Praos performance with/without Leios
- Measure delays under various load conditions
- Verify no Leios starvation under normal operation

### 2.2.4 Freshest-First Delivery Mechanism
**Responsibilities**:
- Enable server-side reordering of replies
- Prioritize young EB requests over old

**Design Decisions**:
- Request/reply protocol rotation
- Streaming vs. atomic replies
- Preemption feasibility

**Detailed Specification**:
- Modified mini-protocol state machines
- Server-side request queue management
- Client-side handling of out-of-order replies

**Alternative Designs**:
- Enriched mini-protocol infrastructure for reordering
- Pros/cons analysis

**Testing Strategy**:
- Simulate ATK-LeiosProtocolBurst
- Measure FFD effectiveness (age distribution of served EBs)
- Verify correctness of out-of-order handling

---

## 2.3 Ledger Layer

### 2.3.1 New Ledger Era (REQ-LedgerNewEra)
**Responsibilities**:
- Define Euler era with all Leios changes
- Hard-fork transition logic

**Design Decisions**:
- Era name and versioning
- Backward compatibility considerations

**Detailed Specification**:
- Era types and instances
- PParams and PParamsUpdate for Euler
- Translation functions from Conway to Euler

**Testing Strategy**:
- Era transition tests
- Backward compatibility verification
- Property tests for era invariants

### 2.3.2 Third Validation Level (REQ-LedgerTxNoValidation, REQ-LedgerCheapReapply)
**Responsibilities**:
- Apply certified transactions without validation
- Ensure significantly cheaper than reapplyTx

**Design Decisions**:
- Which checks to skip vs. retain
- Safety guarantees and assumptions

**Detailed Specification**:
- `notValidateTx` function signature and implementation
- Ledger state update procedure
- Invariants maintained

**Performance Requirements**:
- At least 1 order of magnitude faster than reapplyTx
- Minimize ledger state manipulation

**Testing Strategy**:
- Benchmarks comparing applyTx, reapplyTx, notValidateTx
- Correctness verification (property tests)
- Integration tests with certified EBs

### 2.3.3 Resolved Block Validation (REQ-LedgerResolvedBlockValidation, REQ-LedgerUntickedEBValidation)
**Responsibilities**:
- Accept resolved EB transactions for CertRBs
- Validate EB against pre-update ledger state

**Design Decisions**:
- Interface for passing resolved transactions
- Caller responsibility for resolution

**Detailed Specification**:
- Modified BBODY transition
- Ledger state sequencing (EB validation, then RB update)
- Error handling for missing transactions

**Testing Strategy**:
- Unit tests for BBODY with Leios blocks
- Integration tests with consensus layer
- Property tests for ledger state correctness

### 2.3.4 Voting Committee Management (REQ-LedgerStateVotingCommittee, REQ-LedgerCommitteeSelection)
**Responsibilities**:
- Maintain voting committee in ledger state
- Select persistent voters using Fait Accompli sortition
- Update committee at epoch boundaries

**Design Decisions**:
- Committee representation in ledger state
- Sortition algorithm parameters
- Non-persistent vs. persistent voter distinction

**Detailed Specification**:
- Committee data structure
- Sortition algorithm pseudocode
- TICK transition updates for committee
- Query interface for committee access

**Testing Strategy**:
- Unit tests for sortition algorithm
- Property tests for committee properties (size, stake distribution)
- Integration tests with certificate verification

### 2.3.5 BLS Key Registration (REQ-RegisterBLSKeys, REQ-RotateBLSKeys)
**Responsibilities**:
- Enable SPOs to register/rotate BLS keys
- Track keys in ledger state

**Design Decisions**:
- Registration mechanism (operational certificate vs. other)
- Key rotation policy and constraints

**Detailed Specification**:
- Key registration transaction/certificate format
- Ledger state updates for key registration
- Key rotation rules and validation

**Block Header Access** (REQ-LedgerBlockHeaderAccess):
- If keys in operational certificate, specify header access mechanism
- Consider limiting access to only relevant information

**Testing Strategy**:
- Key registration transaction tests
- Rotation scenarios and edge cases
- Integration with voting committee selection

### 2.3.6 Certificate Verification (REQ-LedgerCertificateVerification)
**Responsibilities**:
- Verify BLS aggregate signatures in certificates
- Use voting committee for verification

**Design Decisions**:
- Verification procedure (threshold, aggregate signature)
- Performance optimizations (batch verification?)

**Detailed Specification**:
- Certificate format and structure
- Verification algorithm (BLS aggregate signature check)
- Error handling for invalid certificates

**Performance Requirements**:
- Verification latency: <100ms per certificate
- Support for batch verification if available

**Testing Strategy**:
- Unit tests with valid/invalid certificates
- Integration tests with voting and block application
- Performance benchmarks

### 2.3.7 Protocol Parameters (REQ-LedgerProtocolParameterAccess, REQ-LedgerProtocolParameterUpdate)
**Responsibilities**:
- Define and manage new Leios protocol parameters
- Support governance updates

**New Parameters** (from CIP-0164):
- EB capacity, voting thresholds, timeouts, etc.

**Detailed Specification**:
- PParams type extension
- PParamsUpdate type extension
- Governance update mechanism
- Default values and validation rules

**Testing Strategy**:
- Parameter update via governance tests
- Validation of parameter ranges
- Impact of parameter changes on protocol behavior

### 2.3.8 Serialization (REQ-LedgerSerializationRB, REQ-LedgerSerializationEB, REQ-LedgerSerializationVote)
**Responsibilities**:
- Define CBOR encodings for RB, EB, Vote

**Design Decisions**:
- Encoding choices (structure, tagging, versioning)
- Backward compatibility

**Detailed Specification**:
- CDDL schemas for each type
- EncCBOR/DecCBOR instances
- Serialization test vectors

**Testing Strategy**:
- Roundtrip property tests
- Cross-implementation compatibility tests
- Size and efficiency verification

---

## 2.4 Cryptography Layer

### 2.4.1 BLS Signature Integration (REQ-BlsTypes through REQ-BlsDSIGNIntegration)
**Responsibilities**:
- Provide BLS12-381 signature primitives
- Support aggregation and batch verification
- Integrate with DSIGN class

**Design Decisions**:
- Variant choice (small public key vs. small signature)
- Rust vs. Haskell implementation balance
- Safety abstractions to prevent misuse

**Detailed Specification**:
- Type definitions (SecretKey, PublicKey, Signature, AggSignature)
- Key generation procedure (secure randomness)
- Proof-of-Possession (PoP) creation and verification
- Sign/Verify API with domain separation
- Aggregate and batch verify APIs
- DSIGN instance implementation

**Security Considerations**:
- Rogue-key attack mitigation (PoP)
- Domain separation to prevent cross-protocol attacks
- Side-channel resistance

**Performance Requirements** (REQ-BlsPerfBenchmarks):
- Single verify: <X ms
- Aggregate verify: <Y ms
- Batch verify: <Z ms (with comparison to individual verifies)

**Conformance** (REQ-BlsConformanceVectors):
- Test vectors from Rust implementation
- IETF draft BLS signature test vectors

**Documentation** (REQ-BlsDocumentation):
- API documentation with usage examples
- Security do's and don'ts section
- Cross-references to CIP-0164 usage

**Testing Strategy**:
- Unit tests for all primitives
- Conformance tests with test vectors
- Performance benchmarks
- Security audits and formal verification (if applicable)

---

## 2.5 Performance & Tracing (P&T)

### 2.5.1 New Observables and Traces
**Responsibilities**:
- Define Leios-specific observables
- Emit traces at appropriate locations
- Expose metrics for monitoring

**Design Decisions**:
- Which events/metrics to trace
- Trace granularity and performance impact
- Compatibility with existing tooling

**Detailed Specification**:
- List of new trace messages (with semantics)
- Metrics definitions (names, types, labels)
- Structured trace format (JSON schemas)
- Trace emission guidelines for developers

**Specification Document**:
- Create and maintain "Leios Observables Specification"
- Define semantics (some generic, some Haskell-specific)
- Input from R&D and simulation insights

**Testing Strategy**:
- Verify trace emission in key scenarios
- Validate trace format and parsing
- Performance impact assessment

### 2.5.2 Analysis Tooling Updates
**Responsibilities**:
- Update `locli` and other tools to parse Leios traces
- Extract performance data from raw traces
- Generate reports and visualizations

**Detailed Specification**:
- New `locli` parsers for Leios messages
- Analysis pipelines for Leios metrics
- Report templates and dashboards

**Testing Strategy**:
- Validate parsing with synthetic traces
- Integration tests with real cluster runs

### 2.5.3 Benchmark Profile Library (cardano-profile)
**Responsibilities**:
- Define Leios benchmark profiles
- Capture all modes of operation and configurations

**Design Decisions**:
- Baseline profile parameters
- Stress test configurations
- Scaled-down model for predicability

**Detailed Specification**:
- Profile definitions in `cardano-profile`
- Parameter sweeps and test matrices
- Success criteria for each profile

### 2.5.4 Benchmark Automation (Nix & Nomad)
**Responsibilities**:
- Deploy and execute Leios benchmarks
- Collect and aggregate results

**Detailed Specification**:
- Nomad job definitions for Leios profiles
- Nix derivations for reproducibility
- Result collection and storage

### 2.5.5 Synthetic Workloads (tx-generator)
**Responsibilities**:
- Generate saturation workloads for Leios
- Maintain stable pressure over benchmark duration

**Design Decisions**:
- Transaction generation patterns
- Rate control and back-pressure handling
- Workload diversity (simple, complex, adversarial)

**Detailed Specification**:
- New workload generators in `tx-generator`
- Configuration parameters
- Validation of workload properties

### 2.5.6 Scaled Leios Model
**Responsibilities**:
- Find scaled-down Leios configuration that predicts full-scale behavior
- Correlate observations across scales

**Design Decisions**:
- Scaling parameters (block size, rate, etc.)
- Invariants to maintain across scales
- Validation methodology

**Process**:
- Iterative refinement with continuous validation
- Coordination between P&T, implementors, and researchers
- Document scaling model and its predictive accuracy

**Testing Strategy**:
- Cross-scale validation experiments
- Sensitivity analysis for scaling parameters
- Regression detection across model versions

### 2.5.7 Comparative Benchmarking Process
**Responsibilities**:
- Structured integration of new features/changes
- Attribute observations to specific changes
- Detect optimizations and regressions

**Detailed Specification**:
- Benchmarking workflow (baseline → change → compare)
- Version tagging and change sets
- Reporting format for comparisons

---

## 2.6 End-to-End Testing

### 2.6.1 Upgraded End-to-End Test Suite
**Responsibilities**:
- Validate existing functionalities after Leios upgrade
- Minimal adjustments to existing tests

**Design Decisions**:
- Which tests require modification
- Backward-compatible block representation in tests

**Detailed Specification**:
- Test suite organization
- Modifications to chain sync tests
- Handling of new block types in assertions

**Testing Strategy**:
- Run full suite on Leios-enabled testnet
- Compare results with pre-Leios baseline

### 2.6.2 Hard-Fork Testing (REQ-HardForkTesting)
**Responsibilities**:
- Test transition from latest mainnet era to Leios era
- Verify continuity of chain and ledger state

**Detailed Specification**:
- Test scenarios (normal, adversarial)
- Validation criteria
- Rollback and recovery testing

**Testing Strategy**:
- Local testnet hard-fork tests
- Persistent testnet (Preview/Preprod) hard-fork tests

### 2.6.3 Automated Upgrade Testing Suite (REQ-AutomatedUpgradeTestSuite)
**Responsibilities**:
- Test node upgrade process from mainnet release to Leios release
- Verify cooperation between mixed-version nodes

**Detailed Specification**:
- Test workflow:
  1. Initialize testnet (Byron era, mainnet node)
  2. Run initial functional tests
  3. Upgrade subset of nodes to Leios-enabled
  4. Run mid-upgrade functional tests
  5. Verify mainnet ↔ Leios node cooperation
  6. Upgrade remaining nodes
  7. Perform hard-fork to Leios
  8. Run post-hard-fork functional tests

**Testing Strategy**:
- Automated CI/CD pipeline for upgrade tests
- Manual validation on testnet clusters
- Regression detection for each step

---

# 3. Cross-Cutting Concerns

## 3.1 Resource Management and Prioritization

### 3.1.1 Scheduling and Priority Enforcement
**Responsibilities**:
- Implement Praos > fresh Leios > stale Leios priority
- Coordinate scheduling across components

**Design Decisions**:
- Centralized scheduler vs. distributed priority hints
- Preemption vs. cooperative scheduling

**Detailed Specification**:
- Priority assignment algorithm
- Thread scheduling modifications
- Resource allocation policies (CPU, memory, disk, network)

**Testing Strategy**:
- Measure Praos impact under various Leios loads
- Verify FFD effectiveness
- Stress tests with ATK-LeiosProtocolBurst

### 3.1.2 GC Pressure Mitigation
**Responsibilities**:
- Minimize GC impact of Leios on Praos
- Use manual memory management where beneficial

**Design Decisions**:
- Which components benefit from manual allocation
- Process isolation vs. shared heap

**Detailed Specification**:
- ByteArray and pinned memory usage guidelines
- Heap profiling targets
- Process isolation architecture (if adopted)

**Experiments** (EXP-LeiosLedgerDbAnalyser):
- Measure GC behavior under EB validation
- Inform mitigation strategies

**Testing Strategy**:
- GC profiling under load
- Comparison with/without mitigations
- Validate no Praos degradation

### 3.1.3 Disk Bandwidth Management
**Responsibilities**:
- Prevent Leios disk I/O from starving Praos
- Rate-limit Leios writes if necessary

**Design Decisions**:
- Rate-limiting strategy and thresholds
- Back-pressure propagation to network layer

**Detailed Specification**:
- Disk I/O prioritization mechanism
- Rate-limiter implementation
- Back-pressure API for network layer

**Experiments** (EXP-LeiosDiffusionOnly):
- Measure disk bandwidth usage under burst
- Validate sufficiency for Praos + Leios

**Testing Strategy**:
- Disk I/O profiling with UTxO HD enabled
- Praos performance under Leios disk load
- Rate-limiter effectiveness tests

---

## 3.2 Security and Attack Resistance

### 3.2.1 Protocol Burst Attack Mitigation (ATK-LeiosProtocolBurst)
**Responsibilities**:
- Withstand adversarial burst of EBs and votes
- Maintain Praos performance during attack

**Threat Model**:
- Adversary withholds EBs/votes, releases all at once
- Worst-case: >1GB burst
- Goal: Minimal impact on Praos, acceptable Leios degradation

**Mitigation Strategies**:
- Prioritization (Praos > fresh Leios > stale Leios)
- Rate-limiting and back-pressure
- GC and disk bandwidth isolation

**Testing Strategy**:
- Simulate ATK-LeiosProtocolBurst in controlled environment
- Measure Praos degradation (latency, throughput)
- Verify system recovery after burst

### 3.2.2 Rogue-Key Attack Prevention (BLS PoP)
**Responsibilities**:
- Prevent adversaries from manipulating aggregate signatures
- Require Proof-of-Possession for all voting keys

**Mitigation**:
- PoP verification at key registration
- Ledger-enforced PoP checks

**Testing Strategy**:
- Unit tests for PoP verification
- Adversarial key registration attempts
- Integration with voting committee selection

### 3.2.3 Network-Level Attacks
**Responsibilities**:
- Resist eclipse, sybil, and DoS attacks
- Maintain diffusion guarantees under adversarial conditions

**Threat Model**:
- Adversary controls subset of peers
- Goals: delay EBs, withhold votes, waste resources

**Mitigation Strategies**:
- Peer diversity and reputation
- Redundant fetching from multiple peers
- Fetch decision logic resilience

**Testing Strategy**:
- Network adversary simulations
- Partition and delay injection tests
- Verification of diffusion bounds (L_diff, etc.)

### 3.2.4 Ledger-Level Invariants
**Responsibilities**:
- Maintain ledger consistency and safety
- Prevent double-spending via invalid EBs

**Invariants**:
- Certificate implies valid EB
- Certified EBs do not conflict
- Ledger state always valid after CertRB application

**Testing Strategy**:
- Property-based testing of ledger transitions
- Formal verification of critical invariants (if feasible)
- Adversarial transaction patterns in EBs

---

## 3.3 Performance and Scalability

### 3.3.1 Throughput Targets
**Goals**:
- Sustain 250 TxkB/s with Leios (vs. 4.5 TxkB/s Praos)
- Maintain low latency for transaction inclusion

**Bottlenecks to Address**:
- Ledger validation performance
- Network diffusion efficiency
- Storage I/O bandwidth

**Performance Budgets**:
- Component-level latency targets
- End-to-end transaction inclusion time

**Validation**:
- Benchmark campaigns with target throughput
- Identify and address bottlenecks iteratively

### 3.3.2 Latency Analysis
**Goals**:
- Characterize inclusion latency under various loads
- Ensure acceptable user experience

**Scenarios**:
- Low load (below Praos capacity): no change vs. Praos
- High load (saturating Leios): ~3-10 minutes (per CIP-0164 simulations)

**Measurement**:
- Instrument transaction submission to inclusion
- Aggregate statistics (median, p95, p99)

**Validation**:
- Compare with CIP-0164 simulation results
- Validate latency SLAs

### 3.3.3 Scalability Path
**Future Considerations**:
- Sharding (Input Block sharding per CIP-0164)
- Further parallelization opportunities
- Protocol parameter tuning

**Design for Future**:
- Modular architecture to accommodate sharding
- Extensibility hooks in EB and certificate formats

---

## 3.4 Observability and Debugging

### 3.4.1 Comprehensive Logging
**Requirements**:
- Log all Leios-specific events
- Include context for debugging (timestamps, block hashes, etc.)

**Design**:
- Structured logging (JSON or similar)
- Log levels (debug, info, warning, error)
- Log rotation and retention policies

**Testing**:
- Verify logs in key scenarios
- Validate completeness and clarity

### 3.4.2 Metrics and Dashboards
**Requirements**:
- Real-time monitoring of Leios health
- Alerting on anomalies

**Metrics** (examples):
- EB diffusion time (per EB)
- Vote aggregation rate
- Certificate inclusion lag
- Storage usage (EBs, votes, transactions)
- Network bandwidth (Praos vs. Leios)

**Dashboards**:
- Grafana dashboards for operators
- Pre-configured alerts

**Testing**:
- Validate metric accuracy
- Test alert conditions

### 3.4.3 Debugging Tools
**Tools**:
- EB/vote inspector (view contents, verify signatures)
- ChainDB query tools (list EBs, votes, certificates)
- Simulation and replay tools for issue reproduction

**Testing**:
- Use tools to investigate issues in testnet
- Validate correctness and usability

---

## 3.5 Configuration and Deployment

### 3.5.1 Configuration Parameters
**Node Configuration**:
- BLS signing key path
- Leios-specific protocol parameters
- Resource limits (memory, disk, network)

**Deployment Considerations**:
- SPO documentation for key generation and registration
- Configuration file format (YAML, JSON)

**Testing**:
- Configuration validation
- Default value sanity checks

### 3.5.2 Deployment Strategy
**Phases**:
1. Testnet deployment (Preview, then Preprod)
2. Monitoring and iteration
3. Mainnet readiness assessment
4. Mainnet hard-fork

**Rollback Plan**:
- Conditions for rollback
- Rollback procedure and tooling

**Testing**:
- Simulate deployment on testnet
- Practice rollback scenarios

---

# 4. Quality Assurance Strategy

## 4.1 Testing Pyramid

### 4.1.1 Unit Tests
**Scope**: Individual functions, data structures, algorithms

**Coverage Goals**: >80% for critical components

**Examples**:
- Vote aggregation logic
- EB closure reconstruction
- BLS signature primitives

**Tools**: Haskell test frameworks (Tasty, HUnit, QuickCheck)

### 4.1.2 Integration Tests
**Scope**: Component interactions, subsystems

**Examples**:
- Block production with Mempool and storage
- Vote production with EB validation
- Network mini-protocols with fetch logic

**Tools**: Custom integration test harness

### 4.1.3 System Tests
**Scope**: End-to-end scenarios on local or persistent testnets

**Examples**:
- Full node synchronization with Leios blocks
- Hard-fork transition
- Upgrade process (mixed-version nodes)

**Tools**: cardano-node-tests, custom test orchestration

### 4.1.4 Property-Based Tests
**Scope**: Invariants, properties, and correctness

**Examples**:
- Ledger state invariants after EB application
- Certificate verification correctness
- Serialization roundtrip properties

**Tools**: QuickCheck, Hedgehog

---

## 4.2 Experimental Validation

### 4.2.1 EXP-LeiosLedgerDbAnalyser
**Goals**:
- Measure CPU and GC cost of EB transaction processing
- Inform resource management decisions

**Method**:
- db-analyser pass on mainnet/testnet data
- Synthetic EB sequences (realistic transactions)
- Separate analysis for full validation vs. reapplication

**Outputs**:
- Mutator time statistics
- GC statistics (allocations, pauses, heap size)
- Performance profiles

**Decision Gates**:
- If GC impact unacceptable → explore mitigations (process isolation, etc.)
- Inform Mempool capacity and cache sizing

### 4.2.2 EXP-LeiosDiffusionOnly
**Goals**:
- Assess network and storage impact of EB diffusion
- Validate sufficiency of ATK-LeiosProtocolBurst mitigation

**Method**:
- Minimally-patched Praos node with only Leios diffusion
- Opaque transactions (no parsing/validation)
- Mock EB arrival from `mainnet` or testnet RBs
- Measure GC stats, disk I/O, network throughput

**Outputs**:
- Event logs and GC profiles
- Disk bandwidth usage
- Network saturation characteristics

**Decision Gates**:
- If Praos degradation observed → refine prioritization or rate-limiting
- Validate EBs can be sustained at target throughput

### 4.2.3 Additional Experiments (as needed)
**Candidates**:
- Voting performance under realistic vote loads
- Certificate verification latency
- Storage layer performance (retrieval, pruning)
- Network topology impact on diffusion

---

## 4.3 Formal Methods

### 4.3.1 Formal Specification (where applicable)
**Scope**:
- Ledger transitions (BBODY, TICK, LEDGER with Leios)
- Voting and certificate logic
- Protocol correctness arguments

**Tools**:
- Agda (formal ledger specs)
- Alloy or TLA+ (protocol-level models)

**Deliverables**:
- Formal spec documents
- Proofs of key properties (safety, liveness)

**Validation**:
- Manual review by formal methods experts
- Comparison with Haskell implementation (property tests)

### 4.3.2 Model Checking (where applicable)
**Scope**:
- Concurrency and locking protocols
- Distributed protocol behaviors (voting, diffusion)

**Tools**:
- TLA+, Spin, or similar

**Outputs**:
- Model correctness proofs
- Counterexamples for edge cases

---

## 4.4 Security Audits

### 4.4.1 Cryptographic Audit (BLS)
**Scope**:
- BLS implementation review
- Side-channel resistance
- Correct usage of primitives

**Auditor**: External cryptography firm

**Deliverables**:
- Audit report
- Remediation plan for findings

### 4.4.2 Protocol Security Audit
**Scope**:
- Leios protocol design review
- Attack vector analysis
- Game-theoretic considerations

**Auditor**: External blockchain security firm

**Deliverables**:
- Security assessment report
- Recommendations for hardening

### 4.4.3 Code Security Review
**Scope**:
- Implementation vulnerabilities (buffer overflows, etc.)
- Concurrency bugs (race conditions, deadlocks)
- Input validation and error handling

**Method**:
- Static analysis tools
- Manual code review
- Fuzzing (if applicable)

**Deliverables**:
- Security bug reports
- Fix verification

---

## 4.5 Performance Benchmarking

### 4.5.1 Baseline Benchmarks
**Goal**: Establish Praos performance baseline

**Benchmarks**:
- Block diffusion latency
- Transaction inclusion latency
- Synchronization time
- Resource usage (CPU, memory, disk, network)

**Execution**: Run on P&T benchmark cluster

### 4.5.2 Leios Benchmarks
**Goal**: Measure Leios performance and compare to baseline

**Benchmarks**:
- EB and RB diffusion latencies
- Vote aggregation and certificate creation time
- Transaction inclusion latency under various loads
- Resource usage with Leios traffic

**Execution**: Run on P&T benchmark cluster with Leios profiles

### 4.5.3 Stress Testing
**Goal**: Validate behavior under adversarial or extreme conditions

**Scenarios**:
- ATK-LeiosProtocolBurst
- Maximum throughput sustained load
- Network partitions and delays
- Mixed-version node scenarios

**Outputs**:
- Performance degradation metrics
- Recovery time
- Failure modes and mitigation effectiveness

### 4.5.4 Regression Testing
**Goal**: Detect performance regressions in CI/CD

**Method**:
- Automated benchmarks on each commit/PR
- Compare to baseline and previous commits
- Alert on significant regressions

**Tools**:
- Continuous benchmarking infrastructure
- Result visualization and analysis

---

## 4.6 Testnet Validation

### 4.6.1 Preview Testnet
**Goals**:
- Early exposure to Leios for developers and integrators
- Identify integration issues
- Gather feedback on node operation

**Deployment**:
- Phased rollout (subset of nodes initially)
- Monitoring and iteration

**Success Criteria**:
- Stable operation for 2+ weeks
- No critical issues identified
- Positive feedback from developers

### 4.6.2 Preprod Testnet
**Goals**:
- Dress rehearsal for mainnet
- Validate hard-fork process
- Load testing with realistic traffic

**Deployment**:
- Full network upgrade
- Coordinated hard-fork

**Success Criteria**:
- Successful hard-fork transition
- No data loss or corruption
- Performance meets targets

### 4.6.3 Community Beta Program
**Goals**:
- Engage community SPOs and developers
- Collect diverse operational feedback
- Build confidence for mainnet

**Method**:
- Public testnet with Leios enabled
- Documentation and support channels
- Incentives for participation

---

## 4.7 Acceptance Criteria

### 4.7.1 Functional Acceptance
**Criteria**:
- All REQ-* requirements satisfied
- Passing functional test suite (>99% pass rate)
- Successful testnet deployments (Preview, Preprod)

### 4.7.2 Performance Acceptance
**Criteria**:
- Throughput: sustain 250 TxkB/s under load
- Latency: transaction inclusion <10 min at saturation, <1 min at low load
- Praos impact: negligible degradation (<5% latency increase)

### 4.7.3 Security Acceptance
**Criteria**:
- No critical or high-severity vulnerabilities unresolved
- Passed cryptographic audit
- Passed protocol security audit
- Demonstrated resilience to ATK-LeiosProtocolBurst

### 4.7.4 Operational Acceptance
**Criteria**:
- SPO documentation complete and validated
- Monitoring and debugging tools available
- Runbooks for common issues
- Successful SPO beta testing

---

# 5. Implementation Roadmap

## 5.1 Phase 0: Foundations (Months 1-3)
**Goals**: Establish architecture, tooling, and core infrastructure

**Deliverables**:
- Finalized technical design document
- C4 container diagram and architecture docs
- Development environment setup
- Initial skeleton implementations (stubs for new components)
- BLS cryptography integration (REQ-BlsTypes through REQ-BlsSerialisation)
- Ledger era definition (REQ-LedgerNewEra)

**Team Composition**: Core architects, crypto engineers, ledger team

**Milestones**:
- [ ] Architecture sign-off
- [ ] BLS primitives functional
- [ ] Euler era defined in ledger codebase

---

## 5.2 Phase 1: Core Components (Months 4-8)
**Goals**: Implement core Consensus and Network components

**Deliverables**:
- Vote production thread (NEW-LeiosVoteProductionThread)
- Vote storage (NEW-LeiosVoteStorage)
- EB storage (NEW-LeiosEbStore)
- Transaction cache (NEW-LeiosTxCache)
- CertRB staging area (NEW-LeiosCertRbStagingArea)
- Block production updates (UPD-LeiosAwareBlockProductionThread)
- Leios mini-protocols (NEW-LeiosMiniProtocols)
- Fetch decision logic (NEW-LeiosFetchDecisionLogic)
- Multiplexer bias (NEW-LeiosPraosMuxBias)
- Unit and integration tests for above

**Team Composition**: Consensus team, Network team

**Milestones**:
- [ ] Vote production functional
- [ ] EB diffusion working end-to-end
- [ ] Block production generates EBs and CertRBs
- [ ] Integration tests passing

---

## 5.3 Phase 2: Ledger Integration (Months 7-10)
**Goals**: Implement ledger changes and certificate verification

**Deliverables**:
- Third validation level (REQ-LedgerTxNoValidation, REQ-LedgerCheapReapply)
- Resolved block validation (REQ-LedgerResolvedBlockValidation, etc.)
- Voting committee management (REQ-LedgerStateVotingCommittee, etc.)
- BLS key registration (REQ-RegisterBLSKeys, etc.)
- Certificate verification (REQ-LedgerCertificateVerification)
- Protocol parameters (REQ-LedgerProtocolParameterAccess, etc.)
- Serialization (REQ-LedgerSerializationRB, etc.)
- Ledger unit and property tests

**Team Composition**: Ledger team, Consensus team (for integration)

**Milestones**:
- [ ] Ledger applies CertRBs correctly
- [ ] Certificate verification functional
- [ ] Property tests passing
- [ ] Integration tests with Consensus passing

---

## 5.4 Phase 3: Experiments and Optimization (Months 9-12)
**Goals**: Run experiments, optimize performance, mitigate risks

**Deliverables**:
- EXP-LeiosLedgerDbAnalyser results
- EXP-LeiosDiffusionOnly results
- Performance profiling and optimization
- GC pressure mitigation (if needed)
- Disk bandwidth management (if needed)
- Benchmarking campaigns (baseline and Leios)

**Team Composition**: P&T team, Consensus team, Ledger team

**Milestones**:
- [ ] Experiment reports completed
- [ ] Resource contention risks assessed
- [ ] Mitigations implemented (if necessary)
- [ ] Performance targets met or path identified

---

## 5.5 Phase 4: Testing and Validation (Months 11-15)
**Goals**: Comprehensive testing, security audits, testnet validation

**Deliverables**:
- Full test suite execution (unit, integration, system, property)
- Formal specification and proofs (if applicable)
- Security audits (crypto, protocol, code)
- Preview testnet deployment and validation
- Preprod testnet deployment and validation
- Community beta program
- Bug fixes and refinements

**Team Composition**: QA team, all engineering teams, external auditors

**Milestones**:
- [ ] Test suite >95% pass rate
- [ ] Security audits completed (no unresolved critical issues)
- [ ] Preview testnet stable for 2+ weeks
- [ ] Preprod testnet hard-fork successful
- [ ] Community feedback incorporated

---

## 5.6 Phase 5: Mainnet Preparation (Months 14-18)
**Goals**: Finalize for mainnet, documentation, operator training

**Deliverables**:
- SPO documentation (key generation, registration, configuration)
- Operator runbooks
- Monitoring dashboards and alerts
- Mainnet deployment plan
- Rollback plan and tooling
- Hard-fork proposal (governance process)

**Team Composition**: All teams, technical writers, DevOps

**Milestones**:
- [ ] Documentation complete and reviewed
- [ ] Mainnet deployment plan approved
- [ ] Hard-fork date announced
- [ ] Pre-hard-fork checklist completed

---

## 5.7 Phase 6: Mainnet Deployment (Month 18+)
**Goals**: Execute mainnet hard-fork and monitor

**Activities**:
- Mainnet node upgrade coordination
- Hard-fork execution
- Intensive monitoring (24/7 for first week)
- Rapid response to issues
- Post-deployment retrospective

**Team Composition**: All teams on-call, incident response team

**Milestones**:
- [ ] Hard-fork successful
- [ ] Mainnet stable for 1+ week
- [ ] Performance targets validated on mainnet
- [ ] No critical issues outstanding

---

# 6. Risk Management

## 6.1 Technical Risks

### 6.1.1 Resource Contention Risks (RSK-*)
**Risks**: GC pressure, disk bandwidth, CPU, network bandwidth

**Mitigation**: Experiments, monitoring, mitigations (process isolation, rate-limiting)

**Contingency**: Rollback plan, parameter tuning

### 6.1.2 Security Vulnerabilities
**Risks**: Undiscovered attack vectors, implementation bugs

**Mitigation**: Security audits, formal methods, testing

**Contingency**: Rapid patching, testnet validation before mainnet fix

### 6.1.3 Performance Degradation
**Risks**: Failure to meet throughput or latency targets

**Mitigation**: Early benchmarking, iterative optimization

**Contingency**: Parameter tuning, protocol adjustments, delayed deployment

### 6.1.4 Integration Issues
**Risks**: Components fail to integrate correctly

**Mitigation**: Incremental integration, continuous integration testing

**Contingency**: Rework architecture, extend timeline

---

## 6.2 Schedule Risks

### 6.2.1 Underestimated Complexity
**Risk**: Implementation takes longer than planned

**Mitigation**: Buffer in schedule, regular progress reviews

**Contingency**: Adjust scope, extend timeline, add resources

### 6.2.2 Dependency Delays
**Risk**: External dependencies (audits, tooling) delayed

**Mitigation**: Early engagement, parallel tracks

**Contingency**: Adjust schedule, find alternatives

### 6.2.3 Testnet Issues
**Risk**: Testnet deployment reveals critical issues

**Mitigation**: Thorough pre-deployment testing

**Contingency**: Iterate on testnet, delay mainnet

---

## 6.3 Operational Risks

### 6.3.1 SPO Adoption
**Risk**: SPOs slow to upgrade or configure correctly

**Mitigation**: Clear documentation, community engagement, beta program

**Contingency**: Extended testnet period, additional support

### 6.3.2 Hard-Fork Coordination
**Risk**: Hard-fork process fails or is contentious

**Mitigation**: Governance process, community communication

**Contingency**: Delay, revise proposal

### 6.3.3 Mainnet Issues Post-Deployment
**Risk**: Unforeseen issues in production

**Mitigation**: Intensive monitoring, rollback plan

**Contingency**: Rapid response, rollback if necessary

---

# 7. Appendices

## Appendix A: Glossary
- Definitions of Leios-specific terms
- Abbreviations and acronyms

## Appendix B: References
- CIP-0164
- Leios research papers
- Related CIPs (CIP-0381, CIP-0135, etc.)
- Relevant Cardano documentation

## Appendix C: C4 Container Diagrams (Detailed)
- Full-page diagrams with annotations
- Multiple views (diff, data flow, voting flow, storage)

## Appendix D: Formal Specifications
- Ledger transition rules (Agda or LaTeX)
- Protocol correctness arguments

## Appendix E: Experimental Results
- EXP-LeiosLedgerDbAnalyser report
- EXP-LeiosDiffusionOnly report
- Benchmark results and analysis

## Appendix F: Security Audit Reports
- Summaries of audit findings
- Remediation status

## Appendix G: Configuration Examples
- Sample node configurations
- SPO setup guides

## Appendix H: Open Questions and Future Work
- Unresolved TODOs from Impact Analysis
- Ideas for future protocol improvements (sharding, etc.)
- Research questions

---

# Document Maintenance

**Version Control**: This document is version-controlled alongside code

**Review Cycle**: Quarterly reviews by technical leadership

**Change Process**: Significant changes require architecture review board approval

**Ownership**: Assigned owners for each major section (team leads)

---

# Conclusion

This Technical Design and Implementation Plan provides a comprehensive blueprint for implementing Leios in cardano-node. It balances detail with flexibility, allowing engineering teams to execute confidently while adapting to discoveries during implementation. Regular review and iteration of this document will ensure it remains a valuable guide throughout the project lifecycle.
