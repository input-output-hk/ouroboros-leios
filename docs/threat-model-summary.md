# Leios Red Team: Initial Summary of Risks and Mitigations

**Date:** 29 October 2026

**Updated:** 10 November 2026

**Project:** Ouroboros Leios

**Version:** 0.1 - draft for review

**Scope:** Threats T1-T34

**Related issue:** [Publish summary of risks and mitigations, #1150](https://github.com/input-output-hk/ouroboros-leios/issues/1150)

## Contents

- [Assessment overview](#assessment-overview)
- [Scope and evidence](#scope-and-evidence)
- [Executive summary](#executive-summary)
- [Threat status](#threat-status)
- [Threat assessments](#threat-assessments)
- [Mitigation validation and remaining analysis](#mitigation-validation-and-remaining-analysis)
- [Assessment methodology and evidence limitations](#assessment-methodology-and-evidence-limitations)

## Assessment overview

This report consolidates the Red Team's existing analysis and experiments against
T1-T34 of the [Leios threat model](threat-model.md). It describes the risk each
threat poses, what the available evidence establishes, and which mitigations
still need validation. It is an initial contribution to issue #1150, not a claim
that the issue's threat-modeling and validation objectives are complete.

## Scope and evidence

The threat inventory is version 0.5 of the threat model, read from
`ouroboros-leios` main at
[`78c44ddd4518203b72e451aa004d1ee1eacd2dd3`](https://github.com/input-output-hk/ouroboros-leios/blob/78c44ddd4518203b72e451aa004d1ee1eacd2dd3/docs/threat-model.md).
The status and risk labels come from the team's status table supplied on 29 October
2026. The assessments below summarize the available Red Team experiment records
and mechanism analysis, including tested conditions, outcomes, and limitations.

The experiments span different environments and prototype revisions:

- **Simulation:** controlled topology, timing, and transaction workloads; useful
  for protocol design and behavior assessments, but not proof of Haskell node implementation correctness.
- **Piranha-only clusters:** real networking between Rust test nodes, with the
  ledger simplifications described in the source reports. These establish attack
  mechanisms and performance effects within that model.
- **Mixed proto-devnet:** adversarial Rust nodes interacting with real Haskell
  nodes. Several reports use one 20% stake adversary and three Haskell pools
  holding 80% collectively; this is a test configuration, not a network-wide
  security threshold.
- **Musashi testnet:** real Haskell implementation and network behavior, with
  less experimental control and potentially confounding changes in load,
  connectivity, and voting participation.

Results on prototypes w32, w34, and w38 are historical observations, not an
assessment of every subsequent release. No new attack or regression experiment
was run to prepare this document. Where a report lacks an exact tested revision,
that limitation remains open. A proposal, a working attack tool, a unit test, and
a successful end-to-end attack are distinct kinds of evidence.

A certificate being observed is also distinct from its inclusion in a ranking
block and application of its transactions by an honest ledger. Likewise, a node
staying alive does not establish that it received and validated the attack.
Negative findings below are limited to the exercised cases and conditions.

## Executive summary

For T1-T34, the supplied status table records four final reports, seven preliminary reports,
six investigations in progress, six threats pending analysis or feasibility
assessment, and eleven threats outside this assessment's scope. These are
reporting states, not counts of independently validated security properties.

The strongest completed implementation checks concern **certificate rejection**.
On the w38 mixed devnet, four certificate variants produced 27 distinct invalid
certificate-bearing blocks that reached honest-ledger validation; all were
rejected and none adopted. Seven of these are the T15 single-signature test,
shared with the T14 report and counted only once. One non-member test run had no
samples reach validation. These results support the tested validation gates,
without establishing that every certificate encoding or context is covered.
See [T14](#t14-include-invalid-certificate-in-rb) and
[T15](#t15-forge-certificate-without-quorum).

**Loss of Leios throughput does not necessarily imply loss of Praos liveness.**
The T10 observation recorded almost no certification during a voting
misconfiguration while ranking blocks continued. T27 simulations demonstrated
recoverable certification disruption under network partition. A related valid-transaction
flood on the w32 testnet coincided with reduced certification; it did not establish
a permanent stall or independently prove the proposed mempool-fragmentation mechanism.
See [T10](#t10-decline-to-vote) and
[T27](#t27-mempool-partitioning-via-network-control).

**Historical implementation defects must be reconciled with the team's supplied
risk labels.** Reports under T11 and T13 record item-count handling faults,
connection disruption, and malformed-transaction process crashes on older
prototypes. The available evidence does not establish a fix revision and
complete regression coverage. Separately,
T12-related tests recorded acceptance and memory retention of correctly signed
votes for unknown targets. These are version-specific findings requiring
closure evidence, not grounds to claim that the current release is vulnerable
or that these risks have been resolved.
See [T11](#t11-create-invalid-eb), [T12](#t12-create-invalid-vote), and
[T13](#t13-reference-invalid-transactions-in-eb).

**Within this assessment's scope, priority validation gaps include selective
data withholding and certified-data availability.** T21 requires validation of
certification availability when data is withheld from selected voters. T22 requires
evidence that delaying certified data to other honest nodes does not persistently
violate the timing assumptions on which Praos depends. Economic incentives,
censorship, and value extraction also require further analysis. The following
sections separate model mitigations from mitigations actually exercised.

## Threat status

The table preserves the team's supplied status and risk labels alongside this
report's evidence assessment. The individual assessments explain
where supporting evidence is incomplete, narrower than the threat, or in tension
with the supplied label.

| Threat # | Threat summary | Team report status | Team risk label | Evidence assessment |
|---|---|---|---|---|
| [T1](#t1-any-threat-to-praos) | Any threat to Praos | out of scope | — | No independent Praos assessment |
| [T2](#t2-vrf-grinding-on-eb-eligibility) | VRF grinding on EB eligibility | out of scope | — | Grinding resistance not assessed |
| [T3](#t3-vrf-grinding-on-voting-eligibility) | VRF grinding on voting eligibility | out of scope | — | Grinding resistance not assessed |
| [T4](#t4-vrf-key-compromise) | VRF key compromise | out of scope | — | Key compromise not assessed |
| [T5](#t5-eb-equivocation) | EB equivocation | prelim | Negative | Direct EB-equivocation coverage and resource impact unestablished |
| [T6](#t6-vote-equivocation) | Vote equivocation | TODO | — | Feasibility and scope unresolved |
| [T7](#t7-double-voting) | Double voting | TODO | — | No completed Haskell result |
| [T8](#t8-bls-key-compromise) | BLS key compromise | out of scope | — | Key theft and recovery not assessed |
| [T9](#t9-decline-to-create-eb) | Decline to create EB | final | Negative | Supporting final report unavailable |
| [T10](#t10-decline-to-vote) | Decline to vote | final | Negative | Praos continued during observed certification loss; incentives unvalidated |
| [T11](#t11-create-invalid-eb) | Create invalid EB | prelim | Negative | Mixed historical results; fix validation pending |
| [T12](#t12-create-invalid-vote) | Create invalid vote | TODO | — | Historical unknown-target vote retention; full assessment pending |
| [T13](#t13-reference-invalid-transactions-in-eb) | Reference invalid transactions in EB | prelim | Negative | Historical crashes; fix validation pending |
| [T14](#t14-include-invalid-certificate-in-rb) | Include invalid certificate in RB | in progress | — | Delivered variants rejected; coverage incomplete and resource cost unquantified |
| [T15](#t15-forge-certificate-without-quorum) | Forge certificate without quorum | final | Negative | Tested one-key/full-committee forgery rejected |
| [T16](#t16-omit-targeted-transactions-from-rb-and-eb) | Omit targeted transactions from RB and EB | ? | — | Scope and feasibility pending |
| [T17](#t17-reorder-transactions-in-eb) | Reorder transactions in EB | in progress | — | No completed economic or implementation result |
| [T18](#t18-insert-or-replace-transactions-in-eb) | Insert or replace transactions in EB | in progress | — | No completed economic or implementation result |
| [T19](#t19-omit-available-eb-certificate-and-fill-rb-with-own-transactions) | Omit available EB certificate and fill RB with own transactions (extractive or defensive) | in progress | — | Narrow historical mechanism test; economic scenario unvalidated |
| [T20](#t20-withhold-announced-eb-or-endorsed-transactions) | Withhold announced EB or endorsed transactions | prelim | Negative | Retry mitigation supported in Rust cluster; Haskell validation pending |
| [T21](#t21-selectively-withhold-data-from-voting-committee) | Selectively withhold data from voting committee | TODO | — | Harness and plans; no completed result |
| [T22](#t22-selectively-withhold-data-from-most-honest-nodes) | Selectively withhold data from most honest nodes | in progress | — | Mechanism described; timing and mitigation validation pending |
| [T23](#t23-withhold-then-release-large-number-of-ebs) | Withhold then release large number of EBs | prelim | Negative | No measured harm at tested scale; sustained congestion untested |
| [T24](#t24-submit-duplicate-transactions) | Submit duplicate transactions | prelim | Negative | Supporting results pending collection |
| [T25](#t25-submit-invalid-transactions) | Submit invalid transactions | prelim | Negative | No isolated real-node result established |
| [T26](#t26-submit-conflicting-transactions) | Submit conflicting transactions | in progress | — | Simulator inference; Haskell validation and resource cost pending |
| [T27](#t27-mempool-partitioning-via-network-control) | Mempool partitioning via network control | final | Positive | Temporary simulated disruption; real-implementation partition validation pending |
| [T28](#t28-honeypot-contract-creating-transaction-races) | Honeypot contract creating transaction races | out of scope | — | Application economics not assessed |
| [T29](#t29-exploit-implementation-differences-between-node-versions) | Exploit implementation differences between node versions | out of scope | — | Adversarial mixed-version behavior not assessed |
| [T30](#t30-coordinate-governance-attacks-to-prevent-hard-fork) | Coordinate governance attacks to prevent hard fork | out of scope | — | Governance mitigations not assessed |
| [T31](#t31-honest-demand-exceeds-spo-storage-capabilities) | Honest demand exceeds SPO storage capabilities | out of scope | — | Long-term storage sustainability not assessed |
| [T32](#t32-silently-accumulate-bls-keys-to-forge-certificate) | Silently accumulate BLS keys to forge certificate | out of scope | — | Adaptive security and rotation effectiveness unresolved |
| [T33](#t33-silently-accumulate-vrf-keys-for-eligibility) | Silently accumulate VRF keys for eligibility | out of scope | — | Adaptive security and rotation effectiveness unvalidated |
| [T34](#t34-fork-to-extract-mev-from-a-recent-block) | Fork to extract MEV from a recent block | ? | — | Scope and feasibility pending; no mitigation validated |

**Legend:** Threat # = identifier in threat model version 0.5; EB = endorser block;
RB = ranking block; VRF = verifiable random function; BLS =
Boneh-Lynn-Shacham signature scheme; SPO = stake pool operator; MEV = maximal
extractable value. Team report status describes report progress: **final** = final
report recorded by the team; **prelim** = preliminary report; **in progress** = active
investigation; **TODO** = pending analysis, not started; **?** = pending analysis
of feasibility or scope; **out of scope** = excluded from this assessment.
Team risk label preserves the team's convention: **Negative** = no risk;
**Positive** = risk identified; **—** = no risk assessment supplied. These labels
do not grade severity. "No risk" records the team's assessment, not a universal guarantee
across untested variants, implementations, or releases. Evidence assessment states
what the reviewed material supports and what remains unresolved; it does not
replace or redefine the team's supplied labels.

## Threat assessments

### T1: Any threat to Praos

**Description.** Leios inherits Praos safety and liveness assumptions. Attacks on
the underlying consensus can therefore affect Leios independently of its added
transaction-processing mechanisms.

**Recommendation.** Maintain the dependency on Praos security analysis and
validate that Leios processing does not invalidate its timing assumptions.

**Assessment.** Out of scope for a separate Praos assessment. This exclusion does
not remove the Leios-specific timing questions assessed under T21-T23 and T27.
No independent Praos security conclusion is made here. Source: [threat model](threat-model.md).

### T2: VRF grinding on EB eligibility

**Description.** Manipulating eligibility randomness may increase the adversary's
block-production opportunities and amplify other threats.

**Recommendation.** Track the threat model's Ouroboros Phalanx research dependency
and its applicability to Leios eligibility.

**Assessment.** Out of scope for this implementation assessment. Randomness
manipulation and grinding resistance require separate protocol and security
analysis. Neither grinding resistance nor the proposed
countermeasure was tested
here. Source: [threat model](threat-model.md).

### T3: VRF grinding on voting eligibility

**Description.** Eligibility manipulation may concentrate voting power beyond the
adversary's nominal stake share.

**Recommendation.** Evaluate the voting-selection implications alongside the
randomness and grinding work referenced by the threat model.

**Assessment.** Out of scope for this implementation assessment. Randomness
manipulation and grinding resistance require separate protocol and security
analysis. No empirical or cryptographic validation of the
mitigation is claimed. Source: [threat model](threat-model.md).

### T4: VRF key compromise

**Description.** Compromised eligibility keys can give an attacker control over
another participant's production or selection opportunities.

**Recommendation.** Apply strong key management and assess operational compromise
and recovery through the responsible security program.

**Assessment.** Out of scope.
The Red Team reports summarized here do not audit
VRF cryptography or key custody. Source: [threat model](threat-model.md).

### T5: EB equivocation

**Description.** A producer can distribute competing endorser-block announcements
to waste resources or divide voting. Exercising this threat requires production
eligibility, valid variant EBs, and ranking blocks announcing their different
hashes to different peers. A relay merely modifying another producer's EB body
creates a hash mismatch, not two valid competing announcements.

**Recommendation.** Exercise conflicting, valid EB announcements with controlled
peer delivery and record each honest node's detection, voting, and chain choice.
Measure resource use and throughput against a matched baseline.

**Assessment.** Preliminary/Negative in the team's supplied status table.
Mechanism analysis is available, but direct EB-equivocation validation and its
resource impact remain unestablished by the evidence summarized here.

### T6: Vote equivocation

**Description.** Replayed or conflicting votes may interfere with certificate
construction. Repeating the same signed message is a duplicate-accounting case;
signing valid votes for competing targets within the same voting context belongs
to [T7](#t7-double-voting). An eligible voter with its signing key can create these
votes without forging a signature.
Whether T6 has a distinct instance depends on the signed fields, election context,
and duplicate-accounting rules of the tested protocol version.

**Recommendation.** Establish the exact signed-message and election context in
the current protocol, then test replay, duplicate accounting, and conflicting
votes against honest receivers.

**Assessment.** Pending analysis. No final feasibility decision or complete
implementation result is available; mechanism analysis alone does not validate
Haskell vote accounting.

### T7: Double voting

**Description.** An eligible voter signs individually valid votes for competing
targets, supplied by producer equivocation or an existing fork. These are distinct
votes, not byte-identical replays. Multiple certificates are not, by themselves,
evidence of conflicting settled ledger histories: certificate inclusion in ranking
blocks, chain selection, and transaction application must also be examined.

**Recommendation.** Construct competing valid proposals and votes, measure quorum
accounting, and verify that honest chain selection and ledger application remain
consistent.

**Assessment.** Pending analysis. No completed Haskell validation of the described
mechanism is established here.
Source: [threat model](threat-model.md).

### T8: BLS key compromise

**Description.** A stolen voting key permits unauthorized signatures. This is
different from submitting an invalid signature or falsifying a signer bitmap.

**Recommendation.** Assess key protection, rotation, and recovery, including the
threat model's defensive-equivocation proposal.

**Assessment.** Out of scope. T14 and T15 test certificate validation; they do not
establish resistance to theft of genuine keys. Source: [threat model](threat-model.md).

### T9: Decline to create EB

**Description.** An eligible producer omits an EB, reducing the additional
throughput available from Leios. The team's supplied status table records
final/Negative. Supporting empirical evidence was unavailable for this summary.

**Recommendation.** Document the tested conditions and observations. Distinguish
continued ranking-block production from lost EB throughput, and validate any
claimed economic deterrent separately.

**Assessment.** Final in the team's supplied status table; the recorded negative
assessment has not been independently confirmed here.

### T10: Decline to vote

**Description.** Missing votes can prevent EBs from reaching quorum even while
ranking-block production continues.

**Evidence.** On Musashi in August 2026, omitted BLS-key configuration and newly
registered, non-voting stake reduced participating weight below the historical
75% quorum threshold. Between 12 August 22:45 and 13 August 05:31 UTC, only two
certified EBs were recorded, while Praos blocks continued. Configuring voting restored sufficient weight
and certification resumed. This was an operational observation, not a controlled
abstention experiment; the threshold describes that deployment.

**Recommendation.** Monitor effective voting participation and key configuration.
Validate incentives separately: continued Praos operation does not demonstrate
that rewards deter abstention.

**Assessment.** Final/Negative in the team's supplied status table. The evidence
supports continued base-chain operation at the observed moderate load despite lost certification;
it does not show that Leios throughput is unaffected by missing quorum.

### T11: Create invalid EB

**Description.** A producer able to announce and serve adversarial EBs can target
byte limits, item limits, or declared-size handling at different processing stages.

**Evidence.** Local w34 tests used a roughly 20%-stake adversarial producer and
three Haskell nodes. A body of approximately 3.8 MB was rejected by the wire-size
guard before decoding or storage: connections closed, but processes survived and
the chain advanced. A self-consistent 13,889-entry manifest passed that byte guard
and was stored, then exceeded a 13,888-entry vector when an honest node served it.
Bounds exceptions disconnected peers; sustained churn stalled the chain, which
resumed within one to two minutes after the attack stopped.

An empty body advertised as 2 MB caused no observed memory growth or disconnection.
Advertising 2 GB did not drive memory toward that declared size, but triggered a
size-mismatch exception and peer disconnection after fetching. In the controlled
repeat, connections recovered between bursts and the chain advanced.

**Recommendation.** Validate semantic item and byte limits before storage, use
total error handling, and repeat boundary tests against the target release.

**Assessment.** Preliminary, with mixed historical evidence. The byte-size and
allocation probes have bounded negative results; item-count and size-mismatch
fixes have not been validated by the reviewed reports.

### T12: Create invalid vote

**Description.** Vote admission must check both cryptographic validity and target
context, while bounding retained state. A current committee-key holder can sign
fresh, arbitrary ranking-block hashes rather than replaying identical votes.

**Evidence.** A related w34 test against three local Haskell nodes submitted such
votes in batches small enough to pass the wire-size guard. Membership and
signature checks accepted them despite the unknown targets. One run grew
from 12 to 129,012 acquired votes per node, with sampled memory rising from about
160 MB to 310 MB and no observed reclaim during a 70-second post-test interval.
The report infers retained-state growth from these observations; it does not
measure internal collection cardinality or demonstrate eventual exhaustion.
The nodes survived; restarting the affected nodes was the documented way to
release accumulated memory. Stopping the sender alone did not reclaim it during
the measured interval.
This is a semantic-admission and lifecycle finding, not evidence of a bad
signature passing verification.

**Recommendation.** Validate target, committee, and temporal context; bound
retained vote state. Test malformed signatures and voter identifiers separately,
including resource cost and recovery.

**Assessment.** Pending analysis for the full threat; related historical
admission/retention behavior reproduced. Fixes for the target release have not
been validated here.

### T13: Reference invalid transactions in EB

**Description.** A producer can announce an EB with unavailable transaction bodies
or serve bodies that match the manifest hashes but are malformed transactions.
Availability and transaction validity require separate checks.

**Evidence.** Unavailable-body tests did not achieve certification in the tested
Rust cluster. In a w34 mixed devnet, a roughly 20%-stake producer instead served
malformed bodies to three Haskell nodes: a byte string appeared where the decoder
expected a transaction-body map. Fetching and certification succeeded, but later
decoding on the forging/tracing path raised a fatal error. Fetch-only crash
reachability remained unconfirmed.
Two independent local runs crashed the same two of three nodes. After disarming
the attack, restarting the affected nodes from their existing databases restored
operation without a genesis reset.

A separate Musashi run directly observed body delivery to the relay serving the
committee; the committee crashes were confirmed by its operators. Neither certification
nor a decoder crash establishes successful application of invalid transactions
to an honest ledger.

**Recommendation.** Use total transaction decoding and validation at the relevant
trust boundaries. Verify both rejection and process survival with confirmed
delivery, including restart conditions; separately verify honest ledger
non-application.

**Assessment.** Preliminary/Negative in the team's supplied status table, with
historical failures requiring explicit reconciliation and a pinned fix/regression record.

### T14: Include invalid certificate in RB

**Description.** A producer can include an invalid certificate in a ranking block,
forcing honest nodes to validate it. Rejection correctness and verification cost
are separate questions.

**Evidence.** Four variants were tested against unmodified w38 Haskell nodes, with
one 20%-stake adversary and three honest pools holding 80% collectively. Each
variant had three runs, each with a fresh devnet and fresh transaction inputs.
For the delivered blocks, headers passed validation before certificate checks.

| Certificate defect | Delivered blocks | Rejection stage and verdict |
|---|---:|---|
| Signer bitmap one byte too long | 9 | Length check: `MalformedSigners` |
| Only out-of-range signer bits | 4 | Committee-weight check: `InsufficientWeight` |
| Wrong ranking-block hash plus signer-set mismatch | 7 | Aggregate signature check: `InvalidSignature` |
| One-key aggregate claiming all committee seats (T15) | 7 | Aggregate signature check: `InvalidSignature` |

**Legend:** Delivered blocks are distinct forged-certificate blocks recorded in
honest-ledger rejection logs, not forge attempts or per-node log counts. All 27
were rejected; none was adopted. T15's seven blocks are shared samples, counted
once. One out-of-range-signers run delivered no samples and adds no rejection
evidence.

The wrong-context variant also mismatched the named signer set; pure message
binding was isolated only in a one-member unit test. Length and weight failures
were rejected before aggregate verification; signature failures reached that
costlier stage. This qualitative ordering does not quantify resource impact.

**Recommendation.** Add malformed aggregate-point coverage and isolate context
binding where feasible. Retain evidence of actual honest validation, rather than
counting adversary-side forge attempts. Under repeated delivered invalid
certificates, compare CPU use, validation latency, queue growth, honest
certification throughput, and recovery against a matched baseline.

**Assessment.** In progress. Tested gates rejected all delivered variants;
garbage/zero aggregates and certificate/body-context combinations are not fully
covered by this report. Verification cost and effects on honest throughput under
repeated attack remain unquantified.

### T15: Forge certificate without quorum

**Description.** The adversary supplied a one-key aggregate while the signer
bitmap claimed all four committee seats. This passed the claimed-weight gate and
tested whether the aggregate was bound to the named signers. The three fresh runs
in [T14](#t14-include-invalid-certificate-in-rb) delivered two, three, and two
blocks respectively; all seven reached signature verification and were rejected
with `InvalidSignature`, with none adopted.

**Recommendation.** Retain this as an interoperability regression for signer-set
binding and repeat it when committee or certificate encoding changes.

**Assessment.** Final/Negative in the team's supplied status table. The tested
one-key/full-committee forgery was rejected. This is an implementation check, not a proof of BLS cryptographic
security or a test of stolen quorum keys.

### T16: Omit targeted transactions from RB and EB

**Description.** A producer can delay selected transactions by omitting them.
The model expects honest mempool persistence and distributed production to limit
censorship, but even temporary delay can affect time-sensitive transactions.
The team's supplied status is undecided.

**Recommendation.** Define the intended censorship duration, adversarial stake,
and workload, including deadline-sensitive transactions, before selecting an
experiment.

**Assessment.** Pending analysis of scope and feasibility; no negative risk
assessment is supplied. Source: [threat model](threat-model.md).

### T17: Reorder transactions in EB

**Description.** A producer's ordering discretion may enable maximal extractable
value and disadvantage users. A larger block creates more opportunities, but
valid ordering changes alone do not establish a ledger-safety violation.

**Recommendation.** Use realistic application transactions to quantify value
extraction and assess application-layer protections such as batch auctions and
slippage limits.

**Assessment.** In progress in the team's supplied status table; conclusions
remain pending. No completed economic or implementation result is established
here. Source: [threat model](threat-model.md).

### T18: Insert or replace transactions in EB

**Description.** A producer may insert competing transactions or replace its
selected contents to capture value. Meaningful impact analysis requires actual
ledger constraints and application economics.

**Recommendation.** Construct a ledger-valid application scenario and measure
user loss and producer gain, including conflicts that prevent both transactions
from succeeding.

**Assessment.** In progress in the team's supplied status table; conclusions
remain pending. The availability of transaction-injection tools does not
establish an economic or implementation result. Source: [threat model](threat-model.md).

### T19: Omit available EB certificate and fill RB with own transactions

**Description.** Dropping an available certificate can sacrifice throughput for
extractive or defensive purposes. In the historical configuration tested, the
immediate successor of an EB's announcing ranking block was the certificate
inclusion opportunity. A producer in that position could omit a certificate even
after the EB reached quorum.

**Evidence.** A 50-node Rust-cluster study compared this suppression with periodic,
untargeted reorganizations, restarting the cluster between configurations. At
approximately 7.1%, 14.3%, and 21.4% adversarial stake, plain suppression remained
near the measurement floor of one event per roughly 14-EB window. Reorganizations
of one to four blocks reduced attributed suppression to zero while causing churn:
they orphaned the adversary's suppressing blocks, sometimes also the target EB's
announcing block, instead of reliably installing a suppressing successor.

Small samples and a fixed seed limit this result. It neither excludes a targeted
reorganization nor validates the full economic scenario. The successor rule and
stake points describe that experiment, not universal protocol bounds.

**Recommendation.** Evaluate the model's proposals to allow transactions alongside
certificates, attach incentives to inclusion, and publish omission statistics.
Test targeted producer choices with realistic application value and timing.

**Assessment.** In progress in the team's supplied status table; conclusions
about the broader threat remain pending. The negative historical mechanism
experiment does not validate incentive compatibility or the proposed
mitigations. Source: [threat model](threat-model.md).

### T20: Withhold announced EB or endorsed transactions

**Description.** Withholding transaction bodies can leave voters unable to validate
an announced EB before the voting deadline.

**Evidence.** Ledger-less Rust-cluster experiments blocked transaction submission
and, in some variants, fetching. A node that requested transactions only once
could miss bodies that its peer acquired later. Retrying once per slot within the
configured fetch window allowed those later bodies to arrive. A 20-node,
diameter-four comparison with 20% adversarial stake offered 80 transactions/s
with link delays up to 300 ms.
Repeated fetching improved observed performance, but near saturation the attack's
effect was difficult to separate from ordinary degradation.

**Recommendation.** Verify timeout, retry, peer-selection, and multi-peer recovery
behavior under bounded bandwidth, with a healthy baseline and real Haskell
validation. Measure fresh-data completion before the voting deadline.

**Assessment.** Preliminary/Negative in the team's supplied status table. Retry
behavior is a supported mitigation in the modeled environment; real-node
validation and throughput bounds remain open.

### T21: Selectively withhold data from voting committee

**Description.** Controlling delivery to selected voters can prevent certification
without withholding data from everyone. The proposed experiment places adversarial
relays at network bridges to withhold data from a chosen voting-weight subset,
then checks whether alternate paths restore delivery before voting closes.
Unlike T22, the intended outcome is to deny certification.

**Recommendation.** Vary targeted voting weight and connection diversity, confirm
attack delivery and a healthy baseline, and measure whether alternate sources
restore data before the deadline. Validate the model's redundant-connectivity
and monitoring mitigations.

**Assessment.** Pending analysis. Tooling and experimental plans are not evidence
that the proposed defenses are sufficient. A completed validation result was not
available for this assessment.

### T22: Selectively withhold data from most honest nodes

**Description.** The adversary supplies enough voters to obtain a certificate
while delaying data to other honest nodes, potentially delaying ranking-chain
processing. The proposed setup gives committee members a prompt delivery path
while placing other honest nodes behind an adversarial relay. It depends on
network position and control of the receivers' alternate paths; merely withholding
from everyone would instead exercise certification denial.

**Recommendation.** Measure certified-data arrival at non-voting honest nodes
under adverse topology and realistic bandwidth. Validate the diffusion allowance
against worst-case origins, not only average propagation, and distinguish
occasional delays from persistent violations of Praos assumptions.

**Assessment.** In progress. A completed validation result was not available;
neither the timing violation nor the proposed mitigation is established here.

### T23: Withhold then release large number of EBs

**Description.** A producer can accumulate EBs and release them together to
compete with fresh traffic for bandwidth and processing.

**Evidence.** A w34 mixed-devnet run withheld 100 genuinely produced EBs over
approximately 3.7 hours, then released them with up to 3.6 hours of staleness and
150 ms link delay. All 100 identifiers appeared in the inspected honest node's
log, but none appeared in its certificate log; the 20 certificates in the release
window concerned fresh EBs. Announcements/offers arrived at roughly 16–20 per
minute, and chain growth continued. There was no bandwidth cap, so this was a
paced acquisition test rather than demonstrated bandwidth saturation. Receiving
stale EBs does not by itself establish the absence of traffic prioritization.

**Recommendation.** Test bandwidth-constrained links and repeated releases,
measure fresh-EB delivery and Praos ranking-block propagation latency at finer
resolution under congestion, and verify traffic prioritization
explicitly. Delay alone does not reproduce bandwidth congestion.

**Assessment.** Preliminary/Negative in the team's supplied status table. No harm
was measured at this scale, and no released EB was certified in the inspected
log. Protection under sustained congestion remains unverified.

### T24: Submit duplicate transactions

**Description.** Repeated submission can waste processing and bandwidth. The
available work establishes transaction-generation and replay tooling and a plan
to submit the same valid signed transaction repeatedly. A completed Haskell
result measuring duplicate admission, propagation, and cost was not available.

**Recommendation.** Attach the existing preliminary evidence, or measure duplicate
admission, propagation, and resource use using a valid transaction. Rejection of
malformed data must not be mistaken for successful duplicate handling.

**Assessment.** Preliminary in the team's supplied status table; supporting
results pending collection.
Pull-based diffusion and duplicate detection remain model mitigations rather than
independently verified outcomes in this consolidation.

### T25: Submit invalid transactions

**Description.** Invalid submissions test validation before propagation and the
cost of rejection. Random malformed bytes may stop at decoding; decodable but
invalid transactions are needed to exercise later validation stages. The
available tooling and plans distinguish these cases, but a completed Haskell
experiment isolating their rejection costs was not available. Ledger-less Rust
clusters emulate validation and cannot establish rejection before propagation.
The EB-carried malformed-data findings in [T13](#t13-reference-invalid-transactions-in-eb)
exercise a different path from transaction submission.

**Recommendation.** Isolate invalid submissions, verify which validation path
rejects them, and compare propagation and resource cost against a matched honest
load.

**Assessment.** Preliminary/Negative in the team's supplied status table. A
dedicated result supporting that label remains unavailable; tooling readiness
does not establish mitigation effectiveness.

### T26: Submit conflicting transactions

**Description.** Different transactions spending the same input can consume work
even though only one may succeed.

**Evidence.** A related [T27](#t27-mempool-partitioning-via-network-control)
simulation used a 10% conflicting workload with one integer input per transaction
and no scripts or collateral. It recorded no repeated finalized transaction
references and inferred single-spend behavior from conflict handling and aggregate
counters; it did not directly assert that at most one finalized transaction spent
each input. Its partition lasted from slot 300 to 900, compared with 300 to 700 in
the conflict-free run, so delay and backlog differences cannot be attributed to
conflicts alone. This evidence does not validate Haskell ledger semantics or
bound real rejection cost.

**Recommendation.** Deliver independently valid conflicting transactions to real
nodes and assert at most one conflicting spend in settled honest history, using
an explicit settlement criterion. Separately measure eventual inclusion of one
candidate after recovery under stated load and timing assumptions, alongside
wasted processing and recovery time.

**Assessment.** In progress. Simulator evidence is relevant but a complete
real-implementation result is pending.

### T27: Mempool partitioning via network control

**Description.** Network control can separate transaction pools and voting
participants, preventing timely quorum and delaying transaction inclusion.

**Evidence.** The primary simulation used 2,685 nodes, seed 0, a conflict-free
120 kB/s workload, and a complete partition during slots 300–700 of a 1,500-slot
run. Neither side held the required 75% voting weight, so certification stalled.
It resumed after reconnection, but average pending-transaction age peaked at
427 seconds. Mempool size returned near baseline about 680 slots after
reconnection; average pending age still ended at 68.5 seconds, versus 16.5 seconds
without the partition. End-of-run finalization was 97.6%, against 97.7% without
the partition; those similar endpoints conceal substantial delay. The separate
conflict-workload limitations are described under [T26](#t26-submit-conflicting-transactions).
An earlier non-recovery result was invalidated by a simulator fetch bug. These
findings remain limited to one seed and topology.

A related w32 Musashi study submitted valid transactions through two unstaked
Haskell relays alongside background transaction generation, without physically
partitioning the network. In one reported trial, eligible but uncertified blocks
increased from 1/14 before the injection to 4/15 during it,
then 7/15 in the designated post-injection interval, before recovering to 2/21.
This was an observational association with temporary certification loss, not an
isolated causal measurement; mempool fragmentation was not directly measured.
The historical eligibility rule was a next-block gap of at least 14 slots and
must not be reused uncritically
for a newer protocol configuration.

**Recommendation.** Validate worst-case diffusion timing and recovery on real
implementations. Extend simulation across seeds, topologies, and recurrent
partitions; isolate transaction-load effects with controlled comparisons. Record
per-input finalized spends to directly check the inferred single-spend behavior.

**Assessment.** Final/Positive in the team's supplied status table. The simulation
demonstrates recoverable certification disruption and prolonged transaction delay
under the tested conditions. Real-implementation partition validation and
mitigation effectiveness remain open.

### T28: Honeypot contract creating transaction races

**Description.** An application can encourage many mutually conflicting
transactions, consuming resources despite only some being eligible to succeed.

**Recommendation.** Assess contract incentives, costs, and realistic user behavior
in an application-focused economic analysis.

**Assessment.** Out of scope. Generic conflicting-transaction tests do not establish
the economics or resource impact of such a contract.
Source: [threat model](threat-model.md).

### T29: Exploit implementation differences between node versions

**Description.** Different node behavior during deployment can cause chain
divergence. Routine Rust/Haskell interoperability work provides useful tooling,
but is not an adversarial mixed-version assessment.

**Recommendation.** Maintain conformance and staged-deployment testing across the
supported release combinations, with explicit divergence checks.

**Assessment.** Out of scope. No cross-version safety conclusion is made by this
report. Source: [threat model](threat-model.md).

### T30: Coordinate governance attacks to prevent hard fork

**Description.** Governance influence or deployment coordination failures can
prevent an upgrade or leave incompatible populations of nodes.

**Recommendation.** Evaluate governance procedures, readiness signaling, and
communication through the relevant governance and rollout reviews.

**Assessment.** Out of scope. Network attack experiments do not validate these
social and organizational mitigations. Source: [threat model](threat-model.md).

### T31: Honest demand exceeds SPO storage capabilities

**Description.** Sustained successful throughput can impose storage requirements
that force less-resourced operators offline.

**Recommendation.** Validate retention, growth, and long-term operating costs
across representative operator hardware before increasing capacity parameters.

**Assessment.** Out of scope. Short attack runs and transient memory measurements
are not evidence of long-term storage sustainability.
Source: [threat model](threat-model.md).

### T32: Silently accumulate BLS keys to forge certificate

**Description.** An adaptive adversary may collect enough genuine signing keys
over time to produce a quorum certificate without visible earlier misuse.

**Recommendation.** Resolve the adaptive-security analysis and evaluate whether
rotation and compromise detection adequately bound usable accumulated keys.

**Assessment.** Out of scope. The threat model explicitly leaves adaptive security
and rotation effectiveness for further research. T15 does not test this case:
a stolen quorum uses genuine signatures. Source: [threat model](threat-model.md).

### T33: Silently accumulate VRF keys for eligibility

**Description.** Accumulating eligibility keys may give the adversary influence
beyond its nominal stake without an immediately observable attack.

**Recommendation.** Validate rotation and compromise assumptions in the adaptive
security model, including the period for which old keys remain useful.

**Assessment.** Out of scope. No empirical or formal mitigation validation is
claimed. Source: [threat model](threat-model.md).

### T34: Fork to extract MEV from a recent block

**Description.** A producer may prefer a competing history when extractable value
outweighs the incentive to extend the current chain. The threat model treats
this as inherited from Praos. Periodic reorganization in the older certificate
suppression experiment did not model application value or a targeted profitable
fork.

**Recommendation.** Assess realistic value, stake, and adoption conditions before
selecting an economic or protocol experiment. Do not treat an unsuccessful
untargeted reorganization as evidence that profitable forking is impossible.

**Assessment.** Pending analysis of feasibility and scope. No Leios-specific
mitigation has been validated here.
See the [threat model](threat-model.md) and the
[suppression experiment in T19](#t19-omit-available-eb-certificate-and-fill-rb-with-own-transactions).

## Mitigation validation and remaining analysis

Issue #1150 asks for confidence in the threat model and in high-importance risks
and mitigations. This draft provides an evidence map; it does not close the
following validation gaps.

| Assessment area | Evidence available | What remains to establish |
|---|---|---|
| Coverage of agreed inventory | All T1-T34 entries represented with the supplied status | Inventory coverage does not establish threat-model completeness |
| Certificate verification | All 27 delivered invalid-certificate blocks rejected on w38 | Remaining malformed encodings and contexts; resource cost and throughput under repeated attack; current-release regression evidence |
| Invalid data handling | Historical rejection, connection-fault, and process-crash observations | Reconcile supplied risk labels with failures; identify fixes and independently reproduce rejection and survival |
| Vote admission and retention | Historical unknown-target acceptance and memory growth | Current target/context checks, bounded lifecycle, and recovery evidence |
| Withholding and diffusion | Rust-cluster retry experiments, burst tests, partition simulations | Realistic bandwidth and topology; certified-data availability to non-voters; validated diffusion allowance |
| Inaction and incentives | Praos continued during voting loss | Quantified throughput impact and evidence for economic deterrence |
| Censorship and value extraction | Model discussion and a narrower suppression experiment | Feasibility, application-value scenarios, and mitigation validation |
| Evidence completeness | Test conditions and outcomes summarized for completed experiments | Establish T9 and T24/T25 results; identify exact tested revisions and complete fix-validation records |

**Legend:** T1-T34 = the threat identifiers covered here; w38 = the prototype
release label recorded by the certificate reports; Praos = the underlying
Ouroboros chain-consensus protocol. "Delivered" means an attack block reached
honest-ledger validation. "Current-release" refers to the release selected for a
new validation campaign, not a claim that one was tested for this draft.

The immediate priorities are to reconcile historical invalid-data findings with
fix evidence, complete the selective-withholding analysis, and validate resource
bounds and diffusion timing under realistic conditions. Economic and adaptive
security work needs explicit coordination with the relevant research and
operational assessments. Each final claim should identify the tested revision,
prerequisites, actual attack delivery, an honest-node outcome, and any remaining
limitations. A lack of samples or missing evidence should remain inconclusive.

## Assessment methodology and evidence limitations

Experimental findings are separated from mechanism analysis and proposed tests.
Each finding identifies the environment, attack exercised, and observed outcome
where these were recorded. Corrected experiments supersede invalid initial
attempts; repeated descriptions of the same samples are not independent evidence.
T14 and T15 share seven delivered blocks, counted once in the combined total.

This is a synthesis of recorded results, not a new experiment or an independent
reanalysis of all raw logs. Observations without available supporting records
are excluded from the empirical conclusions. Missing results remain unresolved,
regardless of the team's supplied risk label.

Prototype release labels do not establish the behavior of later builds. Closing
an implementation finding requires an identified fix and a regression that
confirms attack delivery, rejection, process survival, and recovery as applicable.
