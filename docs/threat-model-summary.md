# Leios Red Team: Initial Summary of Risks and Mitigations

**Date:** 29 October 2026

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
- [Source reports](#source-reports)

## Assessment overview

This report consolidates the Red Team's existing analysis and experiments against
T1-T34 of the [Leios threat model](threat-model.md). It describes the risk each
threat poses, what the available evidence establishes, and which mitigations
still need validation. It is an initial contribution to issue #1150, not a claim
that the issue's threat-modeling and validation objectives are complete.

The report follows the supplied *Anastasia Labs Security Audit Report, version
1.0* (1 September 2026) in structure: an assessment overview, an executive
summary, a compact findings table, and individual Description, Recommendation,
and Resolution sections. That audit is a formatting reference; its findings and
severity ratings are not adopted as Red Team results.

## Scope and evidence

The threat inventory is version 0.5 of the threat model, read from
`ouroboros-leios` main at
[`78c44ddd4518203b72e451aa004d1ee1eacd2dd3`](https://github.com/input-output-hk/ouroboros-leios/blob/78c44ddd4518203b72e451aa004d1ee1eacd2dd3/docs/threat-model.md).
The status and risk labels are the team's status table supplied on 29 October
2026. The report sources are listed below; tracked adversarial reports are pinned
to `leios-adversarial-tools` revision
`103ec6c43ca717bb110b1c1f22fe5680d3b563bf`. Additional local campaign notes are
identified explicitly as unpublished evidence.

The experiments span different environments and prototype revisions:

- **Simulation:** controlled topology, timing, and transaction workloads; useful
  for protocol behavior, but not proof of Haskell implementation correctness.
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

Results on prototypes w32, w34, w36, and w38 are historical observations, not an
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
three investigations in progress, nine threats pending analysis or feasibility
assessment, and eleven threats outside this assessment's scope. These are
reporting states, not counts of independently validated security properties.

The strongest completed implementation checks concern **certificate rejection**.
On the w38 mixed devnet, four certificate variants produced 27 distinct invalid
certificate-bearing blocks that reached honest-ledger validation; all were
rejected and none adopted. Seven of these are the T15 single-signature test,
shared with the T14 report and counted only once. One non-member test run had no
samples reach validation. These results support the tested validation gates,
without establishing that every certificate encoding or context is covered.
([Certificate tests][certificates], [T15 report][single-cert])

**Loss of Leios throughput does not necessarily imply loss of Praos liveness.**
The T10 observation recorded almost no certification during a voting
misconfiguration while ranking blocks continued. T27 simulations demonstrated
recoverable certification disruption under network partition, without a
conflicting-spend safety break in the tested workload. A related valid-transaction
flood on the w32 testnet degraded certification; it did not establish a permanent
stall or independently prove the proposed mempool-fragmentation mechanism.
([T10][inaction], [T27][partition], [Transaction flooding][tx-flood])

**Historical implementation defects must be reconciled with the negative tracker
labels.** Reports under T11 and T13 record item-count handling faults,
connection disruption, and malformed-transaction process crashes on older
prototypes. A later local trial labeled w38 recorded no crashes, but the available notes
do not establish a fix revision and complete regression coverage. Separately,
T12-related tests recorded acceptance and memory retention of correctly signed
votes for unknown targets. These are version-specific findings requiring
closure evidence, not grounds to claim that the current release is vulnerable
or that these risks have been resolved.
([Block bounds][item-limit], [Malformed transactions][dummy],
[Vote accumulation][votes], [Local campaign notes](#local-campaign-notes))

**The highest-impact validation gaps remain selective data withholding and
certified-data availability.** T21 and T22 require evidence that realistic
adversarial delivery cannot cause persistent violations of the timing assumptions
on which Praos depends. Economic incentives, censorship, and value extraction
also lack completed validation in this evidence set. The following sections
separate model mitigations from mitigations actually exercised.

## Threat status

The table preserves the team's supplied status and risk labels. An em dash
represents a blank risk cell in that table. The individual assessments explain
where supporting evidence is incomplete, narrower than the threat, or in tension
with the label.

| Threat # | Threat summary | Status | Risk |
|---|---|---|---|
| [T1](#t1-any-threat-to-praos) | Any threat to Praos | out of scope | — |
| [T2](#t2-vrf-grinding-on-eb-eligibility) | VRF grinding on EB eligibility | out of scope | — |
| [T3](#t3-vrf-grinding-on-voting-eligibility) | VRF grinding on voting eligibility | out of scope | — |
| [T4](#t4-vrf-key-compromise) | VRF key compromise | out of scope | — |
| [T5](#t5-eb-equivocation) | EB equivocation | prelim | Negative |
| [T6](#t6-vote-equivocation) | Vote equivocation | TODO | — |
| [T7](#t7-double-voting) | Double voting | TODO | — |
| [T8](#t8-bls-key-compromise) | BLS key compromise | out of scope | — |
| [T9](#t9-decline-to-create-eb) | Decline to create EB | final | Negative |
| [T10](#t10-decline-to-vote) | Decline to vote | final | Negative |
| [T11](#t11-create-invalid-eb) | Create invalid EB | prelim | Negative |
| [T12](#t12-create-invalid-vote) | Create invalid vote | TODO | — |
| [T13](#t13-reference-invalid-transactions-in-eb) | Reference invalid transactions in EB | prelim | Negative |
| [T14](#t14-include-invalid-certificate-in-rb) | Include invalid certificate in RB | in progress | — |
| [T15](#t15-forge-certificate-without-quorum) | Forge certificate without quorum | final | Negative |
| [T16](#t16-omit-targeted-transactions-from-rb-and-eb) | Omit targeted transactions from RB and EB | ? | — |
| [T17](#t17-reorder-transactions-in-eb) | Reorder transactions in EB | ? | — |
| [T18](#t18-insert-or-replace-transactions-in-eb) | Insert or replace transactions in EB | TODO | — |
| [T19](#t19-omit-available-eb-certificate-and-fill-rb-with-own-transactions) | Omit available EB certificate and fill RB with own transactions (extractive or defensive) | ? | — |
| [T20](#t20-withhold-announced-eb-or-endorsed-transactions) | Withhold announced EB or endorsed transactions | prelim | Negative |
| [T21](#t21-selectively-withhold-data-from-voting-committee) | Selectively withhold data from voting committee | TODO | — |
| [T22](#t22-selectively-withhold-data-from-most-honest-nodes) | Selectively withhold data from most honest nodes | in progress | — |
| [T23](#t23-withhold-then-release-large-number-of-ebs) | Withhold then release large number of EBs | prelim | Negative |
| [T24](#t24-submit-duplicate-transactions) | Submit duplicate transactions | prelim | Negative |
| [T25](#t25-submit-invalid-transactions) | Submit invalid transactions | prelim | Negative |
| [T26](#t26-submit-conflicting-transactions) | Submit conflicting transactions | in progress | — |
| [T27](#t27-mempool-partitioning-via-network-control) | Mempool partitioning via network control | final | Positive |
| [T28](#t28-honeypot-contract-creating-transaction-races) | Honeypot contract creating transaction races | out of scope | — |
| [T29](#t29-exploit-implementation-differences-between-node-versions) | Exploit implementation differences between node versions | out of scope | — |
| [T30](#t30-coordinate-governance-attacks-to-prevent-hard-fork) | Coordinate governance attacks to prevent hard fork | out of scope | — |
| [T31](#t31-honest-demand-exceeds-spo-storage-capabilities) | Honest demand exceeds SPO storage capabilities | out of scope | — |
| [T32](#t32-silently-accumulate-bls-keys-to-forge-certificate) | Silently accumulate BLS keys to forge certificate | out of scope | — |
| [T33](#t33-silently-accumulate-vrf-keys-for-eligibility) | Silently accumulate VRF keys for eligibility | out of scope | — |
| [T34](#t34-fork-to-extract-mev-from-a-recent-block) | Fork to extract MEV from a recent block | ? | — |

**Legend:** Threat # = identifier in threat model version 0.5; EB = endorser block;
RB = ranking block; VRF = verifiable random function; BLS =
Boneh-Lynn-Shacham signature scheme; SPO = stake pool operator; MEV = maximal
extractable value. Status describes report progress: **final** = final report
recorded by the team; **prelim** = preliminary report; **in progress** = active
investigation; **TODO** = pending analysis, not started; **?** = pending analysis
of feasibility or scope; **out of scope** = excluded from this assessment.
Risk uses the team's convention: **Negative** = no risk; **Positive** = risk
identified; **—** = no risk assessment supplied. These labels do not grade
severity. "No risk" records the team's assessment, not a universal guarantee
across untested variants, implementations, or releases; qualifications follow.

## Threat assessments

### T1: Any threat to Praos

**Description.** Leios inherits Praos safety and liveness assumptions. Attacks on
the underlying consensus can therefore affect Leios independently of its added
transaction-processing mechanisms.

**Recommendation.** Maintain the dependency on Praos security analysis and
validate that Leios processing does not invalidate its timing assumptions.

**Resolution.** Out of scope for a separate Praos assessment. This exclusion does
not remove the Leios-specific timing questions assessed under T21-T23 and T27.
No independent Praos security conclusion is made here. Source: [threat model](threat-model.md).

### T2: VRF grinding on EB eligibility

**Description.** Manipulating eligibility randomness may increase the adversary's
block-production opportunities and amplify other threats.

**Recommendation.** Track the threat model's Ouroboros Phalanx research dependency
and its applicability to Leios eligibility.

**Resolution.** Out of scope. Neither grinding resistance nor the proposed
countermeasure was tested in this assessment. Source: [threat model](threat-model.md).

### T3: VRF grinding on voting eligibility

**Description.** Eligibility manipulation may concentrate voting power beyond the
adversary's nominal stake share.

**Recommendation.** Evaluate the voting-selection implications alongside the
randomness and grinding work referenced by the threat model.

**Resolution.** Out of scope. No empirical or cryptographic validation of the
mitigation is claimed. Source: [threat model](threat-model.md).

### T4: VRF key compromise

**Description.** Compromised eligibility keys can give an attacker control over
another participant's production or selection opportunities.

**Recommendation.** Apply strong key management and assess operational compromise
and recovery through the responsible security program.

**Resolution.** Out of scope. The Red Team reports summarized here do not audit
VRF cryptography or key custody. Source: [threat model](threat-model.md).

### T5: EB equivocation

**Description.** A producer can distribute competing endorser-block announcements
to waste resources or divide voting. The tracker records preliminary/Negative.
Implementation notes discuss the mechanism; a related local campaign rerun
confirmed actuation of ranking-header equivocation with certificate suppression,
while honest tips converged and certification continued. This is a narrower
combined experiment, not exhaustive EB-equivocation validation. The initial
campaign attempt was explicitly invalidated for lack of actuation.

**Recommendation.** Exercise conflicting, valid EB announcements with controlled
peer delivery and record each honest node's detection, voting, and chain choice.

**Resolution.** Preliminary. The negative result applies to the tested scenario;
full equivocation-detection coverage remains to be demonstrated.
Sources: [Equivocation notes][equivocation], [local campaign notes](#local-campaign-notes).

### T6: Vote equivocation

**Description.** Conflicting or replayed votes may interfere with certificate
construction. Existing design notes question whether some proposed instances
are merely identical duplicates or overlap T7, rather than an independently
constructible attack. That is a scope argument, not a completed test.

**Recommendation.** Establish the exact signed-message and election context in
the current protocol, then test replay, duplicate accounting, and conflicting
votes against honest receivers.

**Resolution.** Pending analysis. No final feasibility decision or complete
implementation result is available. Source: [Equivocation notes][equivocation].

### T7: Double voting

**Description.** A voter signs for competing blocks or forks. Multiple
certificates are not, by themselves, evidence of conflicting finalized ledger
histories; ranking-chain selection and transaction application must be examined.

**Recommendation.** Construct competing valid proposals and votes, measure quorum
accounting, and verify that honest chain selection and ledger application remain
consistent.

**Resolution.** Pending analysis. The available implementation notes describe an
experiment but do not establish a completed Haskell result.
Sources: [Equivocation notes][equivocation], [threat model](threat-model.md).

### T8: BLS key compromise

**Description.** A stolen voting key permits unauthorized signatures. This is
different from submitting an invalid signature or falsifying a signer bitmap.

**Recommendation.** Assess key protection, rotation, and recovery, including the
threat model's defensive-equivocation proposal.

**Resolution.** Out of scope. T14 and T15 test certificate validation; they do not
establish resistance to theft of genuine keys. Source: [threat model](threat-model.md).

### T9: Decline to create EB

**Description.** An eligible producer omits an EB, reducing the additional
throughput available from Leios. The supplied tracker records final/Negative.
The repository's implementation notes describe the threat, but a standalone
completed results report was not located during this consolidation.

**Recommendation.** Attach the final report and its tested conditions. Distinguish
continued ranking-block production from lost EB throughput, and validate any
claimed economic deterrent separately.

**Resolution.** Final in the team's tracker; supporting report pending collection.
This draft does not invent sample counts or independently confirm the recorded
negative assessment. Sources: supplied status table, [Inaction notes][equivocation].

### T10: Decline to vote

**Description.** On Musashi in August 2026, missing BLS configuration and changing
registered stake left insufficient participating voting weight. Between
12 August 22:45 and 13 August 05:31 UTC, the report records only two certified
EBs, while Praos blocks continued. Certification resumed after voting was
configured. This was an operational observation, not a randomized experiment.

**Recommendation.** Monitor effective voting participation and key configuration.
Validate incentives separately: continued Praos operation does not demonstrate
that rewards deter abstention.

**Resolution.** Final/Negative in the tracker. The evidence supports continued
base-chain operation at the observed moderate load despite lost certification;
it does not show that Leios throughput is unaffected by missing quorum.
Source: [T10 report and collection method][inaction].

### T11: Create invalid EB

**Description.** The preliminary/Negative tracker entry covers several distinct
input-handling questions. The w34 reports found that a body of approximately
3.8 MB was rejected by the wire-size guard without a process crash, and a hollow
body with an inflated declared size did not cause the predicted large allocation.
However, a 13,889-entry manifest reached a serving path with a 13,888-entry vector,
causing bounds exceptions and peer disconnections; sustained churn stalled the
local chain until the attack stopped. Declared-size mismatches also caused
connection faults. These historical failures cannot be erased by the negative
aggregate label.

**Recommendation.** Validate semantic item and byte limits before storage, use
total error handling, and repeat boundary tests against the target release.

**Resolution.** Preliminary, with mixed historical evidence. The byte-size and
allocation probes have bounded negative results; item-count and size-mismatch
fix closure is not established by the reviewed reports.
Sources: [Item-count report][item-limit], [Wire-size report][wire-limit],
[Hollow-body report][hollow], [Attack results][attacks].

### T12: Create invalid vote

**Description.** The tracker leaves the core invalid-vote assessment pending.
A related w34 experiment tested votes that were cryptographically valid but
named unknown ranking-block hashes. Honest nodes accepted them; one run grew
from 12 to 129,012 acquired votes per node, with sampled memory rising from about
160 MB to 310 MB and no observed reclaim during a 70-second post-test interval.
The report infers retained-state growth from these observations; it does not
measure internal collection cardinality or demonstrate eventual exhaustion.
This is a semantic-admission and lifecycle finding, not evidence of a bad
signature passing verification.

**Recommendation.** Validate target, committee, and temporal context; bound
retained vote state. Test malformed signatures and voter identifiers separately,
including resource cost and recovery.

**Resolution.** Pending analysis for the full threat; related historical
admission/retention behavior reproduced. No current-release fix closure is
established here. Source: [Vote-accumulation report][votes].

### T13: Reference invalid transactions in EB

**Description.** Unavailable transaction bodies and available but malformed
bodies produce different outcomes. Phantom-body tests did not achieve
certification in the tested Rust cluster. In contrast, available malformed
transactions caused Haskell process crashes on w34, reproduced in two local
runs with two of three nodes affected. The attack tracker also records a live
Musashi reproduction. Later local w36 campaign notes record a three-node crash;
a subsequent trial labeled w38 records two attack announcements, three surviving nodes,
and no new crash lines. The w38 observation is encouraging but is not a complete
regression or proof that invalid transactions could never be applied.

**Recommendation.** Use total transaction decoding and validation at the relevant
trust boundaries. Verify both rejection and process survival with confirmed
delivery, including restart conditions; separately verify honest ledger
non-application.

**Resolution.** Preliminary/Negative in the tracker, with historical failures
requiring explicit reconciliation and a pinned fix/regression record.
Sources: [Malformed-transaction report][dummy], [Attack results][attacks],
[local campaign notes](#local-campaign-notes).

### T14: Include invalid certificate in RB

**Description.** Four variants were tested against unmodified w38 Haskell nodes:
wrong signer length, out-of-range signer bits, a wrong-context aggregate, and a
single-key aggregate claiming the whole committee. Across the reported runs,
27 distinct blocks reached honest-ledger validation and all were rejected:
nine for signer length, four for insufficient weight, and fourteen for invalid
signature. Seven of those fourteen are the T15 samples, not additional evidence.
One non-member run reached no honest validation and adds no rejection evidence.
On the multi-seat devnet, wrong-context signatures also had a signer-set mismatch;
pure context binding was isolated only in a unit test.

**Recommendation.** Add malformed aggregate-point coverage and isolate context
binding where feasible. Retain evidence of actual honest validation, rather than
counting adversary-side forge attempts.

**Resolution.** In progress. Tested gates rejected all delivered variants;
garbage/zero aggregates and certificate/body-context combinations are not fully
covered by this report. Source: [Combined certificate report][certificates].

### T15: Forge certificate without quorum

**Description.** The adversary supplied a one-key aggregate while the signer
bitmap claimed all four committee seats. In three fresh mixed devnets, seven
distinct forged-certificate blocks reached the honest ledger. Every block was
rejected with `InvalidSignature`, and none was adopted. The test reached the
signature check rather than being stopped by a header-format error.

**Recommendation.** Retain this as an interoperability regression for signer-set
binding and repeat it when committee or certificate encoding changes.

**Resolution.** Final/Negative. The tested one-key/full-committee forgery was
rejected. This is an implementation check, not a proof of BLS cryptographic
security or a test of stolen quorum keys. Source: [T15 report][single-cert].

### T16: Omit targeted transactions from RB and EB

**Description.** A producer can delay selected transactions by omitting them.
The model expects honest mempool persistence and distributed production to limit
censorship, but even temporary delay can affect time-sensitive transactions.
The supplied status is undecided, superseding the older repository tracker that
listed this threat as out of scope.

**Recommendation.** Define the intended censorship duration, adversarial stake,
and workload, including deadline-sensitive transactions, before selecting an
experiment.

**Resolution.** Pending analysis of scope and feasibility; no negative risk
assessment is supplied. Source: [threat model](threat-model.md).

### T17: Reorder transactions in EB

**Description.** A producer's ordering discretion may enable maximal extractable
value and disadvantage users. A larger block creates more opportunities, but
valid ordering changes alone do not establish a ledger-safety violation.

**Recommendation.** Use realistic application transactions to quantify value
extraction and assess application-layer protections such as batch auctions and
slippage limits.

**Resolution.** Pending analysis. The existing notes describe a direction for
work, not a completed economic or implementation result.
Sources: [Value-extraction notes][mev-notes], [threat model](threat-model.md).

### T18: Insert or replace transactions in EB

**Description.** A producer may insert competing transactions or replace its
selected contents to capture value. Meaningful impact analysis requires actual
ledger constraints and application economics.

**Recommendation.** Construct a ledger-valid application scenario and measure
user loss and producer gain, including conflicts that prevent both transactions
from succeeding.

**Resolution.** Pending analysis, not started in the supplied tracker. No result
is inferred from the availability of transaction-injection tools.
Sources: [Value-extraction notes][mev-notes], [threat model](threat-model.md).

### T19: Omit available EB certificate and fill RB with own transactions

**Description.** Dropping an available certificate can sacrifice throughput for
extractive or defensive purposes. An earlier 50-node Rust-cluster study tested
certificate suppression and periodic reorganization. It found no demonstrated
amplification below 25% adversarial stake; the reorganization variant eliminated
the attributed suppression while causing churn. Small samples and a fixed seed
limit that conclusion. It did not test the current threat's full economic
scenario or targeted value extraction.

**Recommendation.** Evaluate the model's proposals to allow transactions alongside
certificates, attach incentives to inclusion, and publish omission statistics.
Test targeted producer choices with realistic application value and timing.

**Resolution.** Pending analysis of the broader threat. The negative historical
mechanism experiment does not validate incentive compatibility or the proposed
mitigations. Sources: [Certificate-suppression experiment][attacks],
[threat model](threat-model.md).

### T20: Withhold announced EB or endorsed transactions

**Description.** Piranha-cluster experiments withheld ordinary transaction
submission and, in some variants, transaction fetching. Certification and
throughput depended strongly on topology, delay, load, and fetch retry behavior.
A one-request implementation could miss transactions that a peer acquired later;
repeated fetching materially improved the results. Near saturation, effects were
hard to distinguish from ordinary network degradation. These were ledger-less
Rust-cluster experiments, not validation of the Haskell implementation.

**Recommendation.** Verify timeout, retry, peer-selection, and multi-peer recovery
behavior under bounded bandwidth, with a healthy baseline and real Haskell
validation. Measure fresh-data completion before the voting deadline.

**Resolution.** Preliminary/Negative. The source reports support an implementation
mitigation in the modeled environment, not a general absence of throughput loss
or complete mitigation validation. Sources: [T20 results][withholding],
[T20 report version 1.1.1][withholding-report].

### T21: Selectively withhold data from voting committee

**Description.** Controlling delivery to selected voters can prevent certification
without withholding data from everyone. A topology-controlled harness exists,
but the reviewed material does not provide a completed result for this threat.

**Recommendation.** Vary targeted voting weight and connection diversity, confirm
attack delivery and a healthy baseline, and measure whether alternate sources
restore data before the deadline. Validate the model's redundant-connectivity
and monitoring mitigations.

**Resolution.** Pending analysis. Tooling and experimental plans are not evidence
that the proposed defenses are sufficient.
Sources: [Selective-withholding material][selective], [threat model](threat-model.md).

### T22: Selectively withhold data from most honest nodes

**Description.** The adversary supplies enough voters to obtain a certificate
while delaying data to other honest nodes, potentially delaying ranking-chain
processing. The available September draft records harness limitations, including
broken certification and unrealistically fast vote spread. A later report
skeleton provides an experimental setup but no raw results. Neither establishes
the intended timing violation or validates its mitigation.

**Recommendation.** Measure certified-data arrival at non-voting honest nodes
under adverse topology and realistic bandwidth. Validate the diffusion allowance
against worst-case origins, not only average propagation, and distinguish
occasional delays from persistent violations of Praos assumptions.

**Resolution.** In progress; outcome and mitigation validation pending.
Sources: [T22 draft][selective-draft], [T22 report skeleton][selective-report],
[threat model](threat-model.md).

### T23: Withhold then release large number of EBs

**Description.** Corrected w34 experiments withheld genuinely produced EBs rather
than relying only on fabricated substitutes. A release of 100 EBs, accumulated
over approximately 3.7 hours with up to 3.6 hours of staleness, was tested with
150 ms link delay. No released EB appeared in the inspected node's certificate
log; fresh certification and chain growth continued. Fetching was paced over
minutes. The report observed stale-data acquisition, which does not by itself
prove the absence of a scheduling priority rule.

**Recommendation.** Test bandwidth-constrained links and repeated releases,
measure fresh-block latency at finer resolution, and verify traffic prioritization
explicitly. Delay alone does not reproduce bandwidth congestion.

**Resolution.** Preliminary/Negative at the tested scale. The observations support
no measured harm and no stale certification in that run; protection under
sustained congestion remains unverified. Source: [T23 report][bursts].

### T24: Submit duplicate transactions

**Description.** Repeated submission can waste processing and bandwidth. The
tracker records preliminary/Negative. The repository contains a duplicate
transaction generator and test plans, but a standalone completed Haskell
results report was not located.

**Recommendation.** Attach the existing preliminary evidence, or measure duplicate
admission, propagation, and resource use using a valid transaction. Rejection of
malformed data must not be mistaken for successful duplicate handling.

**Resolution.** Preliminary in the tracker; supporting results pending collection.
Pull-based diffusion and duplicate detection remain model mitigations rather than
independently verified outcomes in this consolidation.
Sources: [Transaction-threat notes][transaction-notes], [Injection plan][injection].

### T25: Submit invalid transactions

**Description.** Invalid submissions test validation before propagation and the
cost of rejection. The tracker records preliminary/Negative. Combined local
flood trials preserved honest-node survival and tip convergence, but also changed
adversary participation and block supply; they do not isolate the effect of
invalid transaction submission. The EB-carried malformed-data findings in T13
exercise a different path and must not be treated as TxSubmission results.

**Recommendation.** Isolate invalid submissions, verify which validation path
rejects them, and compare propagation and resource cost against a matched honest
load.

**Resolution.** Preliminary. A dedicated, versioned result supporting the full
negative label remains to be attached; combined trials offer only limited
corroboration. Sources: [Transaction-threat notes][transaction-notes],
[local campaign notes](#local-campaign-notes).

### T26: Submit conflicting transactions

**Description.** Different transactions spending the same input can consume work
even though only one may succeed. A related T27 simulation used a 10% conflicting
workload and reported one winner per input and no redundant finalized references.
This supports the model's single-spend property within the simulator; it does not
validate Haskell ledger behavior or bound real rejection cost.

**Recommendation.** Deliver independently valid conflicting transactions to real
nodes, confirm exactly one accepted spend on the honest ledger, and measure
wasted processing and recovery.

**Resolution.** In progress. Simulator evidence is relevant but a complete
real-implementation result is pending.
Sources: [Conflict simulation][conflicts], [Transaction-threat notes][transaction-notes].

### T27: Mempool partitioning via network control

**Description.** Complete simulated network partitions temporarily stalled
certification and accumulated below-quorum EBs, then recovered after healing.
At 120 kB/s offered load, the primary comparison reported 97.6% finalization
against 97.7% for the baseline. A separate 10% conflict workload preserved one
winner per input and recorded zero redundant finalized references. The
consolidated report supersedes an early non-recovery claim caused by a simulator
fetch bug. Results use one seed and topology; the conflict comparison also used
a different partition duration.

A related w32 Musashi study used valid transactions from two sources without
physically partitioning the network. In one reported trial, eligible but
uncertified blocks increased from 1/14 before the injection to 4/15 during it,
then 7/15 in the designated post-injection interval, before recovering to 2/21.
The observation supports a temporary certification effect; mempool fragmentation
is a proposed explanation, not directly measured. The historical eligibility
rule was a next-block gap of at least 14 slots and must not be reused uncritically
for a newer protocol configuration.

**Recommendation.** Validate worst-case diffusion timing and recovery on real
implementations. Extend simulation across seeds, topologies, and recurrent
partitions; isolate transaction-load effects with controlled comparisons.

**Resolution.** Final/Positive in the tracker. The demonstrated risk is temporary
throughput disruption under the tested conditions, not a demonstrated safety
break or permanent denial of service. Real-implementation partition validation
and mitigation closure remain open.
Sources: [Consolidated T27 report][partition], [Conflict run][conflicts],
[Transaction-flood report][tx-flood].

### T28: Honeypot contract creating transaction races

**Description.** An application can encourage many mutually conflicting
transactions, consuming resources despite only some being eligible to succeed.

**Recommendation.** Assess contract incentives, costs, and realistic user behavior
in an application-focused economic analysis.

**Resolution.** Out of scope. Generic conflicting-transaction tests do not establish
the economics or resource impact of such a contract.
Source: [threat model](threat-model.md).

### T29: Exploit implementation differences between node versions

**Description.** Different node behavior during deployment can cause chain
divergence. Routine Rust/Haskell interoperability work provides useful tooling,
but is not an adversarial mixed-version assessment.

**Recommendation.** Maintain conformance and staged-deployment testing across the
supported release combinations, with explicit divergence checks.

**Resolution.** Out of scope. No cross-version safety conclusion is made by this
report. Source: [threat model](threat-model.md).

### T30: Coordinate governance attacks to prevent hard fork

**Description.** Governance influence or deployment coordination failures can
prevent an upgrade or leave incompatible populations of nodes.

**Recommendation.** Evaluate governance procedures, readiness signaling, and
communication through the relevant governance and rollout reviews.

**Resolution.** Out of scope. Network attack experiments do not validate these
social and organizational mitigations. Source: [threat model](threat-model.md).

### T31: Honest demand exceeds SPO storage capabilities

**Description.** Sustained successful throughput can impose storage requirements
that force less-resourced operators offline.

**Recommendation.** Validate retention, growth, and long-term operating costs
across representative operator hardware before increasing capacity parameters.

**Resolution.** Out of scope. Short attack runs and transient memory measurements
are not evidence of long-term storage sustainability.
Source: [threat model](threat-model.md).

### T32: Silently accumulate BLS keys to forge certificate

**Description.** An adaptive adversary may collect enough genuine signing keys
over time to produce a quorum certificate without visible earlier misuse.

**Recommendation.** Resolve the adaptive-security analysis and evaluate whether
rotation and compromise detection adequately bound usable accumulated keys.

**Resolution.** Out of scope. The threat model explicitly leaves adaptive security
and rotation effectiveness for further research. T15 does not test this case:
a stolen quorum uses genuine signatures. Source: [threat model](threat-model.md).

### T33: Silently accumulate VRF keys for eligibility

**Description.** Accumulating eligibility keys may give the adversary influence
beyond its nominal stake without an immediately observable attack.

**Recommendation.** Validate rotation and compromise assumptions in the adaptive
security model, including the period for which old keys remain useful.

**Resolution.** Out of scope. No empirical or formal mitigation validation is
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

**Resolution.** Pending analysis of feasibility and scope. No Leios-specific
mitigation has been validated here.
Sources: [threat model](threat-model.md), [Related suppression experiment][attacks].

## Mitigation validation and remaining analysis

Issue #1150 asks for confidence in the threat model and in high-importance risks
and mitigations. This draft provides an evidence map; it does not close the
following validation gaps.

| Assessment area | Evidence available | What remains to establish |
|---|---|---|
| Threat-model completeness | All T1-T34 entries represented with the supplied status | The model remains a draft; scope exclusions and unresolved research prevent a completeness claim |
| Certificate verification | All 27 delivered invalid-certificate blocks rejected on w38 | Remaining malformed encodings and contexts; current-release regression evidence |
| Invalid data handling | Historical rejection, connection-fault, and process-crash observations | Reconcile tracker labels with failures; identify fixes and independently reproduce rejection and survival |
| Vote admission and retention | Historical unknown-target acceptance and memory growth | Current target/context checks, bounded lifecycle, and recovery evidence |
| Withholding and diffusion | Rust-cluster retry experiments, burst tests, partition simulations | Realistic bandwidth and topology; certified-data availability to non-voters; validated diffusion allowance |
| Inaction and incentives | Praos continued during voting loss | Quantified throughput impact and evidence for economic deterrence |
| Censorship and value extraction | Model discussion and a narrower suppression experiment | Feasibility, application-value scenarios, and mitigation validation |
| Report traceability | Versioned sources for most detailed experiments | Locate T9 final and T24/T25 supporting results; archive local campaign evidence and identify tested revisions |

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

## Source reports

Most detailed evidence is held in the access-controlled
`leios-adversarial-tools` repository. The links below are pinned to the reviewed
revision; readers without access can still read the results and limitations
summarized above. Private source links are not public evidence archives.

- **Threat inventory:** [Threat model version 0.5 at the reviewed main revision](https://github.com/input-output-hk/ouroboros-leios/blob/78c44ddd4518203b72e451aa004d1ee1eacd2dd3/docs/threat-model.md).
- **Status:** team-maintained table supplied for this draft on 29 October 2026;
  it takes precedence over the older [repository status snapshot][old-status].
  The Slack document itself was not directly accessed.
- **T5-T10:** [Implementation and feasibility notes][equivocation];
  [T10 report][inaction] and [collection method][inaction-method].
- **T11/T13:** [Attack-results tracker][attacks],
  [malformed transaction crash][dummy], [item-count bounds][item-limit],
  [wire-size guard][wire-limit], and [hollow-body allocation probe][hollow].
  The wire-size report's earlier open hollow-body question is addressed by the
  later hollow-body report. The attack tracker's older dummy-body negative is
  superseded by its documented delivered-body retest.
- **T12-related:** [Vote-accumulation findings][votes].
- **T14/T15:** [Combined certificate report][certificates],
  [wrong-length certificate results][wrong-length], and [single-key forgery][single-cert].
  The combined report shares the single-key samples with T15.
- **T17-T21:** [Implementation notes][mev-notes],
  [T20 experiment results][withholding], and [T20 report version 1.1.1][withholding-report].
  Older experiment versions are context, not additional independent runs.
- **T21/T22:** [Harness description][selective], [T22 working draft][selective-draft],
  and [T22 report skeleton][selective-report]. These describe readiness and plans,
  not a completed threat validation.
- **T23:** [Initial report with corrected genuine-block runs][bursts].
  Its fabricated-block sweep is distinguished from the subsequent genuine-block
  experiments and is not treated as equivalent evidence.
- **T24-T26:** [Transaction-threat notes][transaction-notes] and
  [transaction-injection plan][injection]; the latter is tooling evidence.
- **T27 and related transaction flooding:** [Consolidated conclusion][partition],
  [primary partition comparison][partition-primary],
  [higher-load run][partition-load], [conflict-workload run][conflicts],
  [partial-cut control][partition-control], and
  [transaction-flood report version 1.1.1][tx-flood]. The consolidated conclusion
  supersedes earlier partition interpretations. The updated transaction-flood
  report is used in preference to the older local preliminary copy; neither
  supplies an independently measured mempool-fragmentation mechanism.

### Local campaign notes

Two additional working-copy files were consulted:
`threats/campaign-2026-09-20/results.md` and
`threats/campaign-2026-09-20/results-auto.md`. They are not tracked at the source
revision above and have no pinned repository link. Only the relevant corrected
observations are summarized here: the valid equivocation rerun, historical
malformed-transaction crashes, the limited w38 no-crash trial, and the limitations
of combined transaction-flood experiments. These observations need an archived,
reviewed evidence record before they can support release-level closure. No
claim of access to missing raw logs or a completed retest is made.

[old-status]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/threat-model-status.md
[equivocation]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/docs/t5-t10-redteam.md
[inaction]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t10/t10.md
[inaction-method]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t10/README.md
[attacks]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/attack-results.md
[dummy]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/eb-attacks/dummy-tx-eb/report.md
[item-limit]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/eb-attacks/oversized-eb/report.md
[wire-limit]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/eb-attacks/huge-ebs/report.md
[hollow]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/eb-attacks/hollow-eb/report.md
[votes]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/voting/vote-accumulation/report.md
[certificates]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t14/README.md
[wrong-length]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t14/wrong-len-cert-results.md
[single-cert]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t15/single-bls-cert.md
[mev-notes]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/docs/t17-t21-redteam.md
[withholding]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t20/T20-test-results.md
[withholding-report]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t20/t20-report-1.1.tex
[selective]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t22/THREATS.md
[selective-draft]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t22/report-draft.md
[selective-report]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t22/t22-report-1.0.tex
[bursts]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t23/report.md
[transaction-notes]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/docs/t22-t26-redteam.md
[injection]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/tx-injection/PLAN.md
[partition]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t27/CONCLUSION.md
[partition-primary]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t27/network-partition.md
[partition-load]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t27/partition-150kb-eu-isolate.md
[conflicts]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t27/partition-120kb-conflict.md
[partition-control]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t27/eu-na-partition-run.md
[tx-flood]: https://github.com/input-output-hk/leios-adversarial-tools/blob/103ec6c43ca717bb110b1c1f22fe5680d3b563bf/threats/t27a/tx-flooding.md
