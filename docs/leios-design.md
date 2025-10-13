---
Title: Leios Technical Design and Implementation Plan
Status: Draft
Version: 0.1
Authors:
  - [To be added]
---

# Introduction

This technical design document bridges the gap between the protocol-level specification (CIP-164) and its concrete implementation in cardano-node. While CIP-164 defines *what* the Leios protocol is and *why* it benefits Cardano, this document addresses *how* to implement it reliably and serve as a practical guide for implementation teams

The scope includes:
- Detailed architecture of node components
- Implementation sequencing and dependencies
- Risk mitigation through modeling and prototyping
- Testing and validation strategies
- Integration with existing and planned protocol upgrades

## Relationship to Other Documents

This document extends:
- **CIP-164**: Protocol-level specification of Leios consensus mechanism
- **Impact Analysis**: High-level requirements and component sketches

## Key Design Principles

1. **Safety First**: Preserve Praos security guarantees throughout deployment
2. **Incremental Delivery**: Enable phased rollout with measurable milestones
3. **Early Validation**: Test critical assumptions before full implementation
4. **Ecosystem Compatibility**: Minimize disruption to existing infrastructure

---

# Protocol Summary and Node Impact

## Leios Protocol Overview

Leios extends Ouroboros Praos by introducing:

- **Ranking Blocks (RBs)**: Extended Praos blocks that announce and certify Endorser Blocks
- **Endorser Blocks (EBs)**: Additional blocks containing transaction references
- **Voting Committee**: BLS signature-based validation of EBs
- **Certificates**: Aggregated proofs of EB validity

**Key timing parameters:**
- $L_\text{hdr} = 1$ slot: Header diffusion period
- $L_\text{vote} = 4$ slots: Voting period
- $L_\text{diff} = 7$ slots: Certificate diffusion period
- Total certification delay: 14 slots (~4.7 minutes)

## Throughput and Performance Targets

Based on CIP-164 simulations:
- **Current Praos**: 4,500 TxB/s
- **Leios Target**: 140,000-300,000 TxB/s
- **Throughput Increase**: 30-65×
- **Transaction Latency** (uncongested): 1-2 minutes mempool to ledger
- **Spatial Efficiency**: >93% (transaction bytes / total stored bytes)

## Core Node Changes Summary

From the Impact Analysis, the following major changes are required:

### Consensus Layer
- **NEW**: Leios block production thread (EB creation alongside RB)
- **NEW**: Vote production and storage system
- **NEW**: EB storage component (volatile and immutable)
- **NEW**: Transaction cache (LRU, age-based)
- **NEW**: CertRB staging area
- **UPD**: Block production logic (dual RB+EB creation)
- **UPD**: Mempool capacity (2× increase)
- **UPD**: LedgerDB (retrieve certified EB closures)
- **UPD**: BlockFetch client (CertRB handling)

### Network Layer
- **NEW**: Leios mini-protocols (LeiosNotify, LeiosFetch)
- **NEW**: Leios fetch decision logic
- **NEW**: Praos/Leios multiplexer bias
- **UPD**: Network prioritization (Praos > fresh Leios > stale Leios)

### Ledger Layer
- **NEW**: Euler era (Leios-specific ledger rules)
- **NEW**: Voting committee state management
- **NEW**: Certificate verification logic
- **NEW**: Transaction validation levels (apply/reapply/noValidate)
- **NEW**: BLS key registration and rotation
- **UPD**: Block structure (RB with EB references and certificates)
- **UPD**: Protocol parameters (Leios-specific parameters)

### Cryptography Layer
- **NEW**: BLS12-381 signature scheme
- **NEW**: Proof-of-Possession (PoP) mechanisms
- **NEW**: Vote and certificate aggregation
- **NEW**: DSIGN integration for BLS

---

# Architecture

## Component Interaction Flow

```
User Transaction Submission
         │
         ▼
   TxSubmission ──────────────────────┐
         │                            │
         ▼                            │
     Mempool                          │
         │                            │
         ├────────────► Transaction   │
         │              Cache         │
         │                            │
         ▼                            │
   Block Production ◄─────────────────┘
         │
         ├──► RB Creation (with EB announcement)
         │
         └──► EB Creation (transaction references)
                │
                ├──► EB Store
                │
                ├──► LeiosNotify ──► Peer Discovery
                │
                └──► LeiosFetch ◄──► Transaction Retrieval
                         │
                         ▼
                   Vote Production
                         │
                         ├──► Vote Storage
                         │
                         └──► Vote Diffusion
                                  │
                                  ▼
                         Certificate Aggregation
                                  │
                                  ▼
                         Certificate in RB'
                                  │
                                  ▼
                              LedgerDB
                                  │
                                  └──► Ledger State Update
```

## Component Specifications

### Consensus Layer Components

#### Block Production Thread (Updated)

**Current State (Praos):**
- Single block production per slot leadership
- Transactions selected from mempool
- VRF-based leader election

**Leios Changes:**
- Dual block production: RB + optional EB
- EB only created if RB cannot accommodate all transactions
- EB announcement hash included in RB header
- Certificate inclusion decision based on timing constraints

**Implementation Considerations:**
- Thread safety for concurrent RB/EB creation
- Memory management for large EB construction
- Deterministic ordering of operations (RB before EB)

#### Vote Production Thread (New)

**Responsibilities:**
- Monitor for new EB announcements
- Determine voting eligibility (persistent/non-persistent)
- Validate EB contents against ledger state
- Generate and sign votes using BLS keys
- Diffuse votes through network layer

**Timing Constraints:**
- Wait 3×$L_\text{hdr}$ after RB announcement (equivocation detection)
- Complete validation within $L_\text{vote}$ period
- Only vote if EB is on tip of current chain

**Implementation Notes:**
```haskell
data VoteProductionState = VoteProductionState
  { vpsEligibleEBs     :: Map SlotNo EBInfo
  , vpsVotingKeys      :: BLSSigningKey
  , vpsCurrentTip      :: RBHeader
  , vpsEBValidation    :: Map EBHash ValidationState
  }

data ValidationState
  = NotStarted
  | InProgress (Async ValidationResult)
  | Completed ValidationResult

voteProductionThread :: VoteProductionState -> IO ()
voteProductionThread state = do
  -- Wake on new EB arrival or validation completion
  -- Check voting eligibility and timing
  -- If eligible and valid, generate and diffuse vote
```

#### Vote Storage Component (New)

**Purpose:**
- Store votes indexed by (EB hash, voter ID)
- Track vote accumulation toward quorum
- Enable certificate construction
- Age out irrelevant votes

**Data Structure:**
```haskell
data VoteStorage = VoteStorage
  { vsVotesByEB      :: Map EBHash (Map VoterID Vote)
  , vsStakeByEB      :: Map EBHash Rational
  , vsCertificates   :: Map EBHash Certificate
  , vsMaxAge         :: NominalDiffTime -- ~10 minutes
  }

-- Track progress toward quorum
calculateQuorumProgress :: EBHash -> VoteStorage -> Rational
insertVote :: Vote -> VoteStorage -> VoteStorage
pruneOldVotes :: SlotNo -> VoteStorage -> VoteStorage
getCertificate :: EBHash -> VoteStorage -> Maybe Certificate
```

**Storage Policy:**
- Keep votes for at most 10 minutes (configurable)
- Discard votes for EBs older than settlement window
- Priority queue by age for efficient pruning

#### Endorser Block Store (New)

**Requirements:**
- Persistent storage of EB bodies and closures
- Volatile/immutable dichotomy like ChainDB
- Support both certified and speculative EBs
- Enable efficient retrieval by hash

**Architecture:**
```haskell
data LeiosEBStore = LeiosEBStore
  { ebsVolatile   :: VolatileEBDB
  , ebsImmutable  :: ImmutableEBDB
  , ebsIndex      :: Map EBHash EBMetadata
  }

data EBMetadata = EBMetadata
  { ebmSlot        :: SlotNo
  , ebmSize        :: Word64
  , ebmCertified   :: Bool
  , ebmLocation    :: StorageLocation
  }

-- Promote certified EBs to immutable storage
certifyEB :: EBHash -> LeiosEBStore -> IO LeiosEBStore

-- Garbage collect uncertified volatile EBs
pruneVolatile :: SlotNo -> LeiosEBStore -> IO LeiosEBStore
```

**Persistence Strategy:**
- Memory-mapped files for transaction data
- SQLite or similar for metadata and indexing
- Separate volatile and immutable storage paths
- Integration with existing ChainDB immutability logic

#### Transaction Cache (New)

**Purpose:**
- Reduce redundant fetching and validation
- LRU eviction policy
- Age-based retention (~1 hour)
- Support concurrent access

**Design:**
```haskell
data LeiosTxCache = LeiosTxCache
  { ltcTransactions :: Map TxId (Tx, TxMetadata)
  , ltcAge          :: Map TxId SlotNo
  , ltcCapacity     :: Word64
  , ltcIndexAge     :: PriorityQueue TxId SlotNo
  }

data TxMetadata = TxMetadata
  { txmValidated    :: Bool
  , txmSeenAt       :: SlotNo
  , txmFirstSeenIn  :: TxSource
  }

data TxSource = FromMempool | FromEB EBHash

-- Insert with LRU eviction
insertTx :: Tx -> TxMetadata -> LeiosTxCache -> LeiosTxCache

-- Mark as validated to reuse work
markValidated :: TxId -> LeiosTxCache -> LeiosTxCache

-- Age-based cleanup
pruneTxCache :: SlotNo -> LeiosTxCache -> LeiosTxCache
```

**Memory Management:**
- Fixed-size byte arrays for transaction storage
- Manual GC pressure management
- Double-buffered memory-mapped files for persistence (optional)

#### CertRB Staging Area (New)

**Purpose:**
- Buffer CertRBs until their EB closures arrive
- Prevent ChainDB pollution with incomplete blocks
- Enable rapid VolDB insertion when EB arrives

**Implementation:**
```haskell
data CertRBStagingArea = CertRBStagingArea
  { crsaPending  :: Map RBHash (RB, Arrival TimeStamp)
  , crsaWaiting  :: Map EBHash RBHash
  , crsaTimeout  :: NominalDiffTime -- Conservative (e.g., 5 min)
  }

-- Stage RB until EB closure available
stageRB :: RB -> CertRBStagingArea -> CertRBStagingArea

-- Release when EB arrives
releaseOnEB :: EBHash -> CertRBStagingArea -> [RB]

-- Timeout handling for missing EBs
pruneTimedOut :: CurrentTime -> CertRBStagingArea -> ([RB], CertRBStagingArea)
```

### Network Layer Components

#### Leios Mini-Protocols (New)

Based on IER table from CIP-164:

**LeiosNotify Protocol:**
```
States: StIdle (Client) → StBusy (Server) → StIdle

Messages:
- MsgLeiosNotificationRequestNext (Client→)
- MsgLeiosBlockAnnouncement (←Server): RB header announcing EB
- MsgLeiosBlockOffer (←Server): EB body available
- MsgLeiosBlockTxsOffer (←Server): Transactions available
- MsgLeiosVotesOffer (←Server): Votes available
```

**LeiosFetch Protocol:**
```
States: StIdle (Client) → St{Block|BlockTxs|Votes|BlockRange} (Server) → StIdle

Messages:
- MsgLeiosBlockRequest (Client→)
- MsgLeiosBlock (←Server)
- MsgLeiosBlockTxsRequest (Client→) with bitmap addressing
- MsgLeiosBlockTxs (←Server)
- MsgLeiosVotesRequest (Client→)
- MsgLeiosVotes (←Server)
- MsgLeiosBlockRangeRequest (Client→) for syncing
- MsgLeiosNextBlockAndTxsInRange (←Server)
- MsgLeiosLastBlockAndTxsInRange (←Server)
```

**Codec Considerations:**
- CBOR serialization for all Leios messages
- Compact bitmap addressing for transaction requests
- Efficient vote bundling in MsgLeiosVotesOffer

#### Leios Fetch Decision Logic (New)

**Responsibilities:**
- Prioritize freshest EBs over stale ones
- Balance load across multiple peers
- Avoid redundant fetches
- Coordinate with vote production needs

**Algorithm:**
```haskell
data FetchDecision = FetchDecision
  { fdEBsToFetch    :: [(Peer, EBHash)]
  , fdTxsToFetch    :: [(Peer, EBHash, TxSet)]
  , fdVotesToFetch  :: [(Peer, Set VoteId)]
  , fdPriority      :: Priority
  }

data Priority = UrgentFresh | Normal | Historical

makeFetchDecision :: 
     [PeerOffer]         -- Available from peers
  -> VoteProductionState -- What we need for voting
  -> ChainSelection      -- What's needed for chain selection
  -> FetchDecision

-- Freshest-first delivery
prioritizeByAge :: [EBHash] -> SlotNo -> [(EBHash, Priority)]
```

#### Praos/Leios Multiplexer (New)

**Purpose:**
- Enforce priority: Praos > fresh Leios > stale Leios
- Prevent Leios from delaying Praos diffusion
- Fair scheduling within priority levels

**Design:**
```haskell
data MuxPriority = PraosPriority | FreshLeios | StaleLeios

data MuxState = MuxState
  { msPraosQueue      :: Queue Message
  , msFreshLeiosQueue :: Queue Message
  , msStaleLeiosQueue :: Queue Message
  , msCurrentBurst    :: Maybe (MuxPriority, [Message])
  }

-- Select next message with priority bias
selectNextMessage :: MuxState -> Maybe (Message, MuxState)

-- Classify Leios messages by age
classifyLeiosMessage :: Message -> SlotNo -> MuxPriority
```

**Configuration:**
- Configurable bias ratio (e.g., 100:10:1 for Praos:Fresh:Stale)
- Starvation prevention for lower priorities
- Burst handling for urgent messages

### Ledger Layer Components

#### Euler Era (New)

**Structure:**
```haskell
data EulerBlock
  = EulerTxRB TxSeq              -- RB with transactions
  | EulerCertRB Certificate      -- RB with EB certificate

data EulerHeader = EulerHeader
  { ehPrevHash      :: Hash EulerHeader
  , ehSlot          :: SlotNo
  , ehBlockNo       :: BlockNo
  , ehAnnouncedEB   :: Maybe EBHash
  , ehAnnouncedEBSize :: Maybe Word32
  , ehCertifiedEB   :: Bool
  -- Standard Praos fields...
  }

data Certificate = Certificate
  { certEBHash       :: EBHash
  , certAggSignature :: BLSSignature
  , certVoters       :: VoterSet
  }
```

**Validation Rules:**
```haskell
-- Apply CertRB by retrieving EB closure
applyCertRB :: Certificate -> LedgerState -> Either ValidationError LedgerState
applyCertRB cert ledger = do
  ebClosure <- retrieveEBClosure (certEBHash cert)
  ledger' <- applyTransactions ebClosure ledger
  validateCertificate cert ledger'
  return ledger'

-- Validate certificate
validateCertificate :: Certificate -> LedgerState -> Either ValidationError ()
validateCertificate cert ledger = do
  -- Check voters are in committee
  validateVoterEligibility (certVoters cert) ledger
  -- Verify BLS aggregate signature
  verifyBLSSignature cert
  -- Check stake threshold
  checkStakeThreshold (certVoters cert) ledger (0.75 :: Rational)
```

#### Voting Committee State (New)

**Management:**
```haskell
data VotingCommittee = VotingCommittee
  { vcPersistentVoters :: Map PoolId (Stake, BLSPubKey)
  , vcTotalStake       :: Rational
  , vcEpoch            :: EpochNo
  }

-- Compute at epoch boundary using Fait Accompli
computeVotingCommittee :: EpochState -> VotingCommittee

-- Check voter eligibility
isEligibleVoter :: 
     PoolId 
  -> SlotNo           -- For non-persistent sortition
  -> VotingCommittee 
  -> Bool
```

#### Transaction Validation Levels (Updated)

**Three validation modes:**
```haskell
-- Full validation (mempool, first EB validation)
applyTx :: Tx -> LedgerState -> Either ValidationError LedgerState

-- Revalidation (mempool refresh, RB validation)
reapplyTx :: Tx -> LedgerState -> Either ValidationError LedgerState

-- Minimal application (certified EB in CertRB)
noValidateTx :: Tx -> LedgerState -> LedgerState
noValidateTx tx ledger = 
  -- Skip expensive checks, only update UTxO
  updateUTxOSet tx ledger
```

**Performance Requirements:**
- `noValidateTx` must be < `reapplyTx` (significantly cheaper)
- `reapplyTx` must be < `applyTx` (~10× faster)
- Budget for up to 12MB of transactions per EB

### Cryptography Layer Components

#### BLS12-381 Integration (New)

**Core Functionality:**
```haskell
data BLSSecretKey = BLSSecretKey ByteString
data BLSPublicKey = BLSPublicKey ByteString
data BLSSignature = BLSSignature ByteString

-- Key generation
generateBLSKeys :: IO (BLSSecretKey, BLSPublicKey)

-- Signing with domain separation
signBLS :: BLSSecretKey -> ByteString -> DomainSeparationTag -> BLSSignature

-- Verification
verifyBLS :: BLSPublicKey -> ByteString -> BLSSignature -> Bool

-- Aggregation
aggregateSignatures :: [BLSSignature] -> BLSSignature
aggregatePublicKeys :: [BLSPublicKey] -> BLSPublicKey

-- Batch verification
batchVerifyBLS :: [(BLSPublicKey, ByteString, BLSSignature)] -> Bool
```

**Proof-of-Possession:**
```haskell
data ProofOfPossession = ProofOfPossession BLSSignature

-- Generate PoP
createPoP :: BLSSecretKey -> BLSPublicKey -> ProofOfPossession

-- Verify PoP
verifyPoP :: BLSPublicKey -> ProofOfPossession -> Bool
```

**DSIGN Integration:**
```haskell
data BLS_DSIGN

instance DSIGNAlgorithm BLS_DSIGN where
  type SeedSizeDSIGN BLS_DSIGN = 32
  type SizeSignKeyDSIGN BLS_DSIGN = 32
  type SizeVerKeyDSIGN BLS_DSIGN = 96
  type SizeSigDSIGN BLS_DSIGN = 48
  
  genKeyDSIGN = generateBLSKeys
  signDSIGN = signBLS
  verifyDSIGN = verifyBLS
```

---

# Risk Assessment and Validation Strategy

## Critical Risks

### Resource Contention Risks

#### RSK-LeiosPraosContentionGC

**Description:** Leios components allocating in the same GHC heap as Praos might increase GC pauses, delaying RB diffusion.

**Impact:** HIGH - Could violate Praos $\Delta$ assumptions and compromise chain security.

**Mitigation Strategies:**
1. **Early validation via EXP-LeiosLedgerDbAnalyser:**
   - Measure GC behavior for realistic EB transaction sequences
   - Quantify mutator time and GC overhead
   - Establish safe EB size limits

2. **Process isolation (if needed):**
   - Separate Leios validation into dedicated process
   - UTxO-HD-like IPC for ledger state access
   - Accept overhead cost for GC isolation

3. **Monitoring and alerting:**
   - Instrument GC statistics in node telemetry
   - Alert on anomalous GC pause times
   - Adaptive EB production throttling

#### RSK-LeiosPraosContentionDiskBandwidth

**Description:** Simultaneous Leios writes (EBs, votes, transactions) and Praos/Ledger operations might saturate disk I/O.

**Impact:** MEDIUM-HIGH - Especially with UTxO-HD where ledger state is on disk.

**Mitigation Strategies:**
1. **Rate limiting:**
   - Limit Leios disk write rate with back-pressure to network
   - Priority I/O scheduling for Praos operations

2. **Buffering and batching:**
   - Memory buffer for EB writes before flushing
   - Batch vote storage writes

3. **Validation via EXP-LeiosDiffusionOnly:**
   - Measure disk I/O under ATK-LeiosProtocolBurst
   - Quantify impact on Praos operations
   - Tune buffer sizes and rate limits

#### RSK-LeiosLedgerOverheadLatency

**Description:** Processing 15000% of a Praos block worth of transactions in bursts might introduce unexpected latency.

**Impact:** MEDIUM - Affects vote timing and certificate generation.

**Mitigation Strategies:**
1. **Benchmarking via EXP-LeiosLedgerDbAnalyser:**
   - Process realistic EB-sized transaction sequences
   - Measure both full validation and reapplication
   - Profile CPU and memory pressure

2. **Implementation optimization:**
   - Lazy evaluation where safe
   - Transaction validation result caching
   - Parallel validation of independent transactions (future)

### Protocol Security Risks

#### RSK-TimingViolation

**Description:** Network conditions might violate timing assumptions ($\Delta_\text{EB}$, $\Delta_\text{RB}$, etc.).

**Impact:** CRITICAL - Could compromise Praos security properties.

**Mitigation Strategies:**
1. **Conservative parameterization:**
   - Use 95th percentile network measurements
   - Add safety margins to all timing parameters
   - Start with conservative values and tighten based on empirical data

2. **Monitoring and detection:**
   - Track diffusion times in telemetry
   - Alert on timing violations
   - Adaptive parameter adjustment (future)

3. **Testnet validation:**
   - Run adversarial scenarios on testnet
   - Measure worst-case diffusion times
   - Validate timing assumptions under load

#### RSK-CertificateVulnerability

**Description:** BLS signature scheme vulnerabilities or implementation bugs could compromise vote integrity.

**Impact:** CRITICAL - Could enable invalid EB certification.

**Mitigation Strategies:**
1. **Formal verification:**
   - Agda specification of certificate validation
   - Property-based testing of BLS operations
   - Cross-implementation test vectors

2. **External audit:**
   - Third-party cryptographic review
   - Penetration testing of voting system
   - Bug bounty program

3. **Gradual rollout:**
   - Enable voting but don't rely on certificates initially
   - Parallel validation in early testnets
   - Incremental trust in cryptographic components

### Operational Risks

#### RSK-SPOAdoption

**Description:** SPOs might not adopt Leios due to increased operational complexity or resource requirements.

**Impact:** MEDIUM - Reduced decentralization or delayed rollout.

**Mitigation Strategies:**
1. **Clear documentation and tooling:**
   - Step-by-step upgrade guides
   - Automated BLS key generation and registration
   - Monitoring dashboards for Leios-specific metrics

2. **Phased rollout:**
   - Initial testnet deployment with early adopter SPOs
   - Mainnet activation only after >80% testnet participation
   - Fallback mechanisms if adoption is insufficient

3. **Incentive alignment:**
   - Ensure Leios improves SPO profitability at scale
   - No penalties for non-participation in early phases
   - Clear communication of long-term economic benefits

## Assumptions to Validate Early

### Network Assumptions

1. **$\Delta_\text{EB}^{\text{O}}$ < 3 seconds**: Optimistic EB diffusion
   - **Validation method:** EXP-LeiosDiffusionOnly on testnet
   - **Metrics:** 95th percentile diffusion time across nodes
   - **Success criteria:** < 2.5 seconds for 12MB EBs

2. **$\Delta_\text{EB}^{\text{W}}$ < 20 seconds**: Worst-case certified EB transmission
   - **Validation method:** Adversarial testnet scenario with withheld EBs
   - **Metrics:** Maximum diffusion time from 25% to 100% of honest stake
   - **Success criteria:** < 18 seconds under ATK-LeiosProtocolBurst

3. **Praos $\Delta$ unchanged**: Leios doesn't delay RB diffusion
   - **Validation method:** Parallel RB+EB diffusion measurement
   - **Metrics:** RB diffusion time with/without Leios overlay
   - **Success criteria:** < 5% increase in RB diffusion time

### Computational Assumptions

1. **$\Delta_\text{reapply}$ < $\Delta_\text{applyTxs}$**: EB reapplication is cheaper than transaction validation
   - **Validation method:** EXP-LeiosLedgerDbAnalyser with mainnet slices
   - **Metrics:** CPU time for reapply vs. apply on same transaction sets
   - **Success criteria:** Reapply < 50% of apply time

2. **Per-EB Plutus budget**: 500× Praos block limit feasible
   - **Validation method:** Plutus-heavy workload simulations
   - **Metrics:** CPU utilization, validation time, GC pressure
   - **Success criteria:** < 80% CPU utilization on 4 vCPU nodes


## Validation Approach

The validation strategy follows a clear progression:

1. **Analytical Validation**: Use EXP-LeiosLedgerDbAnalyser to quantify ledger operation costs and validate computational assumptions
2. **Component Prototyping**: Implement BLS cryptography and EXP-LeiosDiffusionOnly to validate network assumptions  
3. **Integration Testing**: Combine components on private testnets with adversarial scenario testing
4. **Public Testnet**: Deploy to Preview/Preprod with load testing and SPO participation
5. **Mainnet Readiness**: Final parameter tuning, security audit, and ecosystem validation

This progression ensures critical assumptions are validated early through prototypes before committing to full implementation, reducing the risk of discovering fundamental issues late in development.

---

# Implementation Roadmap

## Implementation Philosophy

**Progression Strategy:**
1. **Simulations** (already completed): Validate protocol design and parameters
2. **Prototypes**: Build focused experiments to validate critical assumptions early
3. **Implementation**: Full node implementation guided by validated assumptions
4. **Public Testnet**: Deploy and validate at scale with real SPO participation

This approach prioritizes early risk mitigation through targeted prototypes before committing to full implementation.

## Implementation Phases

### Phase 0: Foundation and Validation

**Objectives:**
- Establish development infrastructure
- Implement BLS cryptography layer
- Validate critical assumptions through prototypes

**Key Deliverables:**
- BLS12-381 integration in cardano-base (key generation, signing, verification, aggregation)
- EXP-LeiosLedgerDbAnalyser (quantify ledger operation costs for EB-sized batches)
- EXP-LeiosDiffusionOnly (validate network timing assumptions)
- Simulation refinement based on mainnet measurements

**Success Criteria:**
- BLS operations meet performance requirements
- Ledger validation times within safe bounds ($\Delta_\text{reapply}$ < 1s)
- Network diffusion times validate protocol parameters ($\Delta_\text{EB}^{\text{O}}$ < 3s)

### Phase 1: Core Consensus

**Objectives:**
- Implement essential consensus layer changes
- Enable basic RB+EB block production
- Build storage infrastructure

**Key Deliverables:**
- Updated block production (dual RB+EB creation)
- Leios EB Store (volatile and immutable storage)
- Transaction Cache (LRU eviction, validation result caching)
- CertRB Staging Area (buffer incomplete blocks)

**Success Criteria:**
- RB+EB production functional on devnet
- EB storage persistence validated
- CertRB chain selection working correctly

### Phase 2: Network Layer

**Objectives:**
- Implement Leios mini-protocols
- Enable EB and vote diffusion
- Enforce Praos>Leios priority

**Key Deliverables:**
- LeiosNotify and LeiosFetch mini-protocols
- Leios fetch decision logic (freshest-first prioritization)
- Praos/Leios multiplexer (priority enforcement)

**Success Criteria:**
- EB diffusion functional on devnet
- Vote diffusion working correctly
- RB diffusion unaffected by Leios traffic

### Phase 3: Voting and Certification

**Objectives:**
- Implement committee voting
- Enable certificate generation
- Integrate with ledger validation

**Key Deliverables:**
- Vote production thread (eligibility, validation, diffusion)
- Vote storage and aggregation
- Euler era ledger rules (CertRB validation, certificate verification)
- BLS key management tooling

**Success Criteria:**
- Voting functional on devnet
- Certificates generated and validated correctly
- Full Leios protocol operational end-to-end

### Phase 4: Optimization and Hardening

**Objectives:**
- Performance optimization
- Security hardening
- Operational tooling

**Key Deliverables:**
- Performance optimizations (lazy evaluation, caching, I/O batching)
- Monitoring and observability (metrics, dashboards, alerting)
- SPO tooling and documentation
- Adversarial testing (protocol burst, equivocation, timing violations)

**Success Criteria:**
- Performance targets met (140-300 TxkB/s)
- Security audit passed
- SPO operational readiness validated

### Phase 5: Public Testnet

**Objectives:**
- Deploy to public testnets
- Validate with real SPO participation
- Finalize mainnet parameters

**Key Deliverables:**
- Preview testnet deployment
- Load testing with synthetic workloads
- Preprod testnet deployment and hard fork rehearsal

**Success Criteria:**
- Stable operation for multiple epochs
- SPO participation >50%
- No critical issues identified
- Mainnet readiness validated

## Dependencies and Critical Path

**Critical Path:**
```
BLS Crypto → Prototypes → Core Consensus → Network Layer → Voting → Hardening → Testnet
  (Phase 0)    (Phase 0)     (Phase 1)       (Phase 2)    (Phase 3)  (Phase 4)  (Phase 5)
```

**Parallelization Opportunities:**
- Network layer development can begin once EB storage design is finalized
- Ledger era definition can proceed alongside voting logic implementation
- Optimization work can start on completed components during later phases

**External Dependencies:**
- Ledger team for Euler era definition and validation rules
- Cryptography team for BLS implementation and security audit
- Network team for mini-protocol review
- Research team for formal verification
- Performance & Testing team for benchmarking infrastructure

---

# Prototype and Testnet Strategy

## Prototype Philosophy

**"Testing can never prove the absence of a bug, but it can increase confidence."**

Our prototyping strategy follows a progression:
1. **Isolated component testing**: Unit and property-based tests
2. **Integration testing**: Component interactions on controlled devnets
3. **Adversarial testing**: Attack scenario simulations
4. **Scale testing**: Load and stress testing on testnets
5. **Mainnet rehearsal**: Hard fork simulation on Preprod

## Key Prototypes

### EXP-LeiosLedgerDbAnalyser

**Purpose:** Quantify ledger operation costs for EB-sized transaction batches.

**Methodology:**
1. Extract mainnet ledger snapshots at various epochs
2. Construct synthetic EB-sized transaction sequences (12MB worth)
3. Measure `applyTx`, `reapplyTx`, and `noValidateTx` performance
4. Profile CPU usage, memory allocation, GC statistics
5. Vary transaction complexity (script-heavy, script-light, etc.)

**Metrics to Collect:**
- CPU time per transaction (μs/tx)
- GC pause frequency and duration
- Memory allocation rate
- Peak memory usage
- Plutus execution time (if applicable)

**Success Criteria:**
- $\Delta_\text{reapply}$ < 1 second for 12MB EB
- `noValidateTx` < 10% of `reapplyTx` time
- GC pauses < 50ms p99
- Validate $\Delta_\text{EB}^{\text{O}}$ assumptions

**Deliverable:** Report with performance models and safe parameter ranges.

### EXP-LeiosDiffusionOnly

**Purpose:** Validate network diffusion assumptions without full validation.

**Design:**
- Minimally-patched Praos node with Leios diffusion only
- Mocked EB validation (always valid)
- Random transaction contents (for size, not semantics)
- Track RB and EB diffusion times separately

**Test Scenarios:**
1. **Baseline:** Normal operation with honest block production
2. **High load:** Saturated EBs every slot
3. **ATK-LeiosProtocolBurst:** Withheld EBs released simultaneously
4. **Mixed:** Concurrent RB and EB diffusion

**Metrics:**
- EB diffusion time (95th percentile)
- RB diffusion time (95th percentile, with/without Leios)
- Network bandwidth utilization
- CPU usage (diffusion logic only)
- GC statistics

**Success Criteria:**
- RB diffusion < 5 seconds (unchanged from Praos)
- EB diffusion < 3 seconds (optimistic case)
- No GC pauses > 100ms during diffusion

**Deliverable:** Validated network timing parameters and topology recommendations.

### Integration Prototypes

**Incremental Feature Integration**

Build up functionality incrementally on a private devnet through key milestones:

**Block Production:** Enable dual RB+EB creation, verify EB announcement in headers, test mempool integration

**EB Diffusion:** Enable LeiosNotify and LeiosFetch protocols, verify freshest-first delivery, measure diffusion times

**Voting:** Enable vote production and diffusion, verify eligibility determination, measure quorum achievement rates

**Certification:** Enable certificate generation and CertRB validation, verify end-to-end transaction flow

**Testing Strategy:** 10-20 node devnet with realistic topology, automated transaction submission, failure injection (partitions, crashes), comprehensive monitoring

### Adversarial Prototypes

**ATK-LeiosProtocolBurst**

**Scenario:** Adversary withholds multiple EBs and releases simultaneously.

**Test Design:**
1. Adversarial node(s) with 10-25% stake
2. Withhold 5-10 valid EBs over 10 minutes
3. Release all EBs simultaneously
4. Measure impact on honest nodes

**Metrics:**
- Honest node CPU and memory spikes
- GC pause times during burst
- EB diffusion time during burst
- Vote production success rate
- RB diffusion delay (if any)

**Success Criteria:**
- RB diffusion < 6 seconds (< 20% increase)
- All honest nodes process burst within 30 seconds
- No node crashes or OOM errors
- Vote production continues normally after burst

**Equivocation Attack**

**Scenario:** Adversary creates multiple EBs for the same slot.

**Test Design:**
1. Adversarial node creates 2+ EBs per slot
2. Diffuse to different parts of network
3. Verify honest nodes detect equivocation
4. Ensure no votes cast for equivocating EBs

**Metrics:**
- Equivocation detection latency
- False positive rate (honest EBs rejected)
- Network overhead from equivocation diffusion
- Vote casting behavior post-detection

**Success Criteria:**
- 100% detection within $3 \times L_\text{hdr}$ = 3 slots
- Zero false positives
- No votes cast for equivocating slot

**Timing Violation Attacks**

**Scenario:** Adversary attempts to violate timing assumptions through strategic delay.

**Test Design:**
1. Network partition to delay EB diffusion
2. Adversary releases EB just before voting deadline
3. Measure honest node behavior

**Success Criteria:**
- Honest nodes correctly refuse to vote if validation incomplete
- No safety violations despite timing stress
- Network recovers after partition heals

## Testnet Deployment Strategy

### Preview Testnet

**Purpose:** Early public testing with SPO participation.

**Configuration:**
- Conservative protocol parameters (lower throughput initially)
- Longer timing periods ($L_\text{vote}$ = 6, $L_\text{diff}$ = 10)
- Smaller EB size limit (8MB initially)

**Testing Focus:**
1. SPO onboarding and operational procedures
2. BLS key management and registration
3. Monitoring and alerting validation
4. Ecosystem integration testing (indexers, explorers)

**Success Criteria:**
- 50+ SPOs successfully running Leios nodes
- 10+ epochs of stable operation
- No critical bugs or safety violations
- Positive SPO feedback on operational complexity

### Load Testing on Preview

**Workload Scenarios:**

**Scenario 1: Sustained High Throughput**
- Target: 150 TxkB/s for 24 hours
- Transaction mix: 70% simple, 20% script, 10% heavy-script
- Measure: Latency, throughput, resource usage

**Scenario 2: Bursty Demand**
- Alternate between 50 TxkB/s and 200 TxkB/s hourly
- Measure: Mempool behavior, EB utilization, latency variation

**Scenario 3: Script-Heavy**
- 80% transactions with Plutus scripts
- Target: 100 TxkB/s
- Measure: CPU usage, validation times, GC pressure

**Scenario 4: Adversarial Load**
- Mix of valid and invalid transactions
- Equivocation attempts
- Measure: Resilience, resource waste, detection rates

**Metrics Collection:**
- Transaction inclusion latency (p50, p95, p99)
- EB certification rate
- Vote participation rate
- Node resource usage (CPU, memory, disk, network)
- Chain quality metrics (forks, rollbacks)

### Preprod Testnet

**Purpose:** Mainnet rehearsal with production configuration.

**Configuration:**
- Mainnet-equivalent protocol parameters
- Full EB size (12MB)
- Target throughput: 200 TxkB/s

**Testing Focus:**
1. Hard fork activation mechanics
2. Cross-client compatibility (if other implementations exist)
3. Ecosystem readiness (wallets, dApps, indexers)
4. Rollback and recovery scenarios
5. Monitoring and operational playbooks

**Hard Fork Rehearsal:**
- Announce hard fork 2 epochs in advance
- Test SPO upgrade procedures
- Verify hard fork boundary epoch transition
- Validate backward compatibility of interfaces

**Success Criteria:**
- Successful hard fork with >95% SPO participation
- 5+ epochs of stable post-fork operation
- All ecosystem partners report compatibility
- No critical issues identified

### Testnet Exit Criteria

Before mainnet deployment, all of the following must be satisfied:

**Functional:**
- [ ] All protocol features operational
- [ ] Certificate validation working correctly
- [ ] Vote production and diffusion functional
- [ ] Ledger state updates correct

**Performance:**
- [ ] Throughput targets met (140-300 TxkB/s)
- [ ] Latency acceptable (<2 min p95 uncongested)
- [ ] Resource usage within bounds (<80% CPU, <16GB RAM)
- [ ] GC pauses acceptable (<100ms p99)

**Security:**
- [ ] No safety violations in adversarial testing
- [ ] Timing assumptions validated empirically
- [ ] Equivocation detection 100% effective
- [ ] BLS cryptography audit complete

**Operational:**
- [ ] SPO documentation complete and validated
- [ ] Monitoring dashboards functional
- [ ] Incident response playbooks tested
- [ ] Rollback procedures validated

**Ecosystem:**
- [ ] Indexers and explorers compatible
- [ ] Wallets and dApps tested
- [ ] Client interfaces backward compatible
- [ ] Migration guides published

---

# Protocol Interactions

## Synergies with Peras

Peras and Leios share several design elements that enable synergistic development:

### Common Infrastructure

**Shared Components:**
1. **BLS Signature Scheme:**
   - Both protocols use BLS12-381 for voting
   - Shared cryptographic infrastructure
   - Common key management tooling
   - Unified audit and testing

2. **Voting Mechanisms:**
   - Similar sortition-based committee selection
   - Overlapping vote diffusion requirements
   - Potential for unified vote aggregation logic

3. **Priority Scheduling:**
   - Peras votes also need prioritization over Leios
   - Shared multiplexer design: Peras > Praos > Leios
   - Common freshest-first delivery mechanisms

### Development Coordination

**Parallel Development Strategy:**
```
           Peras                      Leios
             │                          │
             ├─── BLS Crypto ───────────┤  (Shared)
             │                          │
             ├─── Voting Logic ─────────┤  (Coordinate)
             │                          │
             ├─── Network Priority ─────┤  (Coordinate)
             │                          │
        (Checkpoint                (Throughput
         Voting)                    Scaling)
```

**Integration Considerations:**
- Leios vote production thread can be generalized for Peras votes
- Network multiplexer handles three priority levels: Peras > Praos > Leios
- Shared telemetry and monitoring infrastructure

### Combined Benefits

With both Peras and Leios deployed:
- **Faster finality** via Peras checkpointing
- **Higher throughput** via Leios EBs
- **Better security** through voting committee diversity
- **Unified cryptographic framework** reduces complexity

**Deployment Sequencing:**
- Option A: Deploy Leios first, add Peras later (prioritizes throughput)
- Option B: Deploy Peras first, add Leios later (prioritizes finality)
- Option C: Joint deployment (maximum benefit, higher complexity)

**Recommendation:** Deploy Leios first to address economic sustainability concerns, then add Peras for faster finality. This sequencing:
- Addresses immediate throughput bottleneck
- Validates BLS infrastructure before Peras relies on it
- Enables incremental complexity management

## Interactions with Genesis

Genesis (Ouroboros Genesis) enables nodes to bootstrap from the genesis block without trusted checkpoints. Leios requires the following considerations for Genesis compatibility:

**Key Considerations:**
- Syncing nodes must fetch both RBs and their certified EBs
- LeiosFetch `MsgLeiosBlockRangeRequest` enables efficient batch fetching during sync
- EB closures needed to validate chain density
- Chain density calculations must include transactions from certified EBs (RB-only view underestimates chain quality)
- Certified EBs must be stored permanently alongside RBs
- Immutable storage grows at ~13TB/year at sustained 200 TxkB/s throughput
- Uncertified EBs can be pruned after settlement window
- Parallel fetching from multiple peers critical for sync performance
- Genesis nodes must understand Euler era blocks and track EB certification status
- Initial Leios deployment can use trusted snapshots; full Genesis integration follows after Leios stabilization

## Future Protocol Extensions

Linear Leios (CIP-164) serves as a solid foundation for future scaling enhancements. The design provides natural extension points while avoiding unsolved research problems.

### Straight-Forward Extension Points

**Decoupled EB Production:**
- Current design couples EB production with RB production (each RB announces at most one EB)
- Future: EBs could be produced independently of RBs, increasing parallelism
- Extension path: Network protocols already separate RB and EB diffusion; EB store supports arbitrary arrival patterns
- Benefit: Higher throughput through better resource utilization

**Input Blocks (Three-Tier Structure):**
- Full Leios research protocol adds Input Blocks: IB → EB → RB
- Extension path: Transaction cache and EB store reusable; network protocols extensible; ledger rules can add IB validation layer
- Benefit: Potential for 3-10× additional throughput improvement
- Note: Requires solving concurrent transaction conflicts (see below)

**Dynamic Parameter Adaptation:**
- Future: Adjust $L_\text{vote}$, $L_\text{diff}$, EB sizes based on observed conditions
- Extension path: Parameters already on-chain and governance-updatable; telemetry infrastructure exists; conservative initial parameters leave optimization room

### Unsolved Research Problems

**Conflicting Transactions:**

Higher concurrency (decoupled EBs, Input Blocks) introduces a fundamental challenge: concurrent block production creates transactions that conflict by spending the same UTxO inputs. Only one conflicting transaction can be included in the ledger, wasting network and computational resources on invalidated transactions. Adversaries can exploit this to amplify resource waste.

**Proposed Mitigations Remain Open Problems:**
- **UTxO space sharding**: Requires solving dynamic rebalancing, cross-shard coordination, and adversarial distribution patterns
- **Transaction collateralization**: Impacts user experience and capital efficiency without eliminating all conflicts  
- **Mempool coordination protocols**: Vulnerable to adversarial non-compliance and may negate throughput gains

**Current Approach:** Linear Leios deliberately avoids these problems through sequential, deterministic transaction processing. Future extensions requiring concurrency must demonstrate viable, production-ready solutions to conflict handling before deployment. The ecosystem benefits from proven throughput gains today rather than waiting years for resolution of open research questions.

---

# Appendices

## Appendix A: Glossary

| Term | Definition |
|------|------------|
| **RB** | Ranking Block - Extended Praos block that announces and certifies EBs |
| **EB** | Endorser Block - Additional block containing transaction references |
| **CertRB** | Ranking Block containing a certificate |
| **TxRB** | Ranking Block containing transactions |
| **BLS** | Boneh-Lynn-Shacham signature scheme using elliptic curve BLS12-381 |
| **PoP** | Proof-of-Possession - Prevents rogue key attacks in BLS aggregation |
| **$L_\text{hdr}$** | Header diffusion period (1 slot) |
| **$L_\text{vote}$** | Voting period (4 slots) |
| **$L_\text{diff}$** | Certificate diffusion period (7 slots) |
| **FFD** | Freshest-First Delivery - Network priority mechanism |
| **ATK-LeiosProtocolBurst** | Attack where adversary withholds and releases EBs simultaneously |

## Appendix B: References

1. **CIP-164**: Ouroboros Linear Leios - Greater transaction throughput  
   https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md

2. **Leios Impact Analysis**: High-level component design  
   https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/ImpactAnalysis.md

3. **Leios Research Paper**: Ouroboros Leios: Design Goals and Concepts  
   https://iohk.io/en/research/library/papers/ouroboros-leios-design-goals-and-concepts/

4. **Leios Formal Specification**: Agda implementation  
   https://github.com/input-output-hk/ouroboros-leios/tree/main/formal-spec

5. **BLS Signatures Specification**:  
   https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/Specification.md

6. **Peras Technical Design**: Synergistic protocol  
   https://tweag.github.io/cardano-peras/peras-design.pdf

7. **Ouroboros Genesis**: Bootstrap mechanism  
   https://iohk.io/en/research/library/papers/ouroboros-genesis-composable-proof-of-stake-blockchains-with-dynamic-availability/

8. **Cardano Ledger Formal Specification**:  
   https://github.com/IntersectMBO/formal-ledger-specifications/

9. **Ouroboros Network Specification**:  
   https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf

10. **UTxO-HD Design**:  
    https://github.com/IntersectMBO/ouroboros-consensus/blob/main/docs/website/contents/for-developers/utxo-hd/index.md

---

## Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 0.1 | 2025-01-XX | [Author] | Initial draft |

---

*This document is a living artifact and will be updated as implementation progresses, new risks are identified, and validation results become available.*
