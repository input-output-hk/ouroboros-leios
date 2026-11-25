# Leios Red Team: Initial Summary of Risks and Mitigations

**Date:** 29 October 2026

**Updated:** 24 November 2026

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

The assessment covers version 0.5 of the public threat model at
[`78c44ddd4518203b72e451aa004d1ee1eacd2dd3`](https://github.com/input-output-hk/ouroboros-leios/blob/78c44ddd4518203b72e451aa004d1ee1eacd2dd3/docs/threat-model.md).
The assessments summarize tested conditions, observed outcomes, mechanism
analysis, and remaining validation gaps.

The experiments span different environments and prototype revisions:

- **Simulation:** A Rust implementation with controlled topology, timing, and transaction workloads; useful for protocol design and behavior assessments, but not proof of Haskell node implementation correctness. Simulated networking.
- **Emulation:** Rust test nodes running complete Leios protocols with real networking,
  simplified ledger behavior, including emulated validation. These experiments
  establish attack mechanisms and performance effects within that model.
- **Mixed proto-devnet:** Adversarial Rust nodes interacting with real Haskell
  nodes on a single machine with traffic shaped network delays. Several experiments
  use one 20% stake adversary and three Haskell pools holding 80% collectively in a test configuration complete with Haskell relays.
- **Musashi testnet:** Adversarial Rust nodes running on hosted servers interacting with real Haskell nodes on the Mushahi test network. As many as 10 nodes, configured both with and without relays, performed coordinated attacks on Haskell nodes (typically the IOG nodes); this focussed primarily on attacks at scale.

Results on prototypes w32, w34, and w38 are historical observations, not an
assessment of every subsequent release. The November 2026 w43 invalid-EB and
duplicate-submission campaigns identify their tested revisions and re-test the
earlier w34 invalid-EB findings on a newer release; they are recorded campaigns,
not a regression suite. No new experiment was run to prepare this document.
Where the exact tested revision is unknown, release-specific conclusions remain
limited. A proposal, a working attack tool,
a unit test, and a successful end-to-end attack are distinct kinds of evidence.

A certificate being observed is also distinct from its inclusion in a ranking
block and application of its transactions by an honest ledger. Likewise, a node
staying alive does not establish that it received and validated the attack.
Negative findings below are limited to the exercised cases and conditions.

## Executive summary

T1-T34 comprise final assessments, investigations still in progress, pending analysis or feasibility assessment, and twelve threats outside scope. Assessment status does not imply
that every security property or mitigation has been validated.

The strongest completed implementation checks concern **certificate rejection**.
On the w38 mixed devnet, four certificate variants produced 27 distinct invalid
certificate-bearing blocks that reached honest-ledger validation; all were
rejected and none adopted. Seven of these are the T15 single-signature test,
also covered under T14 and counted only once. One non-member test run had no
samples reach validation. These results support the tested validation gates,
without establishing that every certificate encoding or context is covered. See
[T14](#t14-include-invalid-certificate-in-rb) and
[T15](#t15-forge-certificate-without-quorum).

**Loss of Leios throughput does not necessarily imply loss of Praos liveness.**
The T10 observation recorded almost no certification during a voting
misconfiguration while ranking blocks continued. T27 simulations demonstrated
recoverable certification disruption under complete regional partition, with
backlogs draining after reconnection at both tested loads. A related valid-transaction
flood on the w32 testnet coincided with reduced certification; it did not establish
a permanent stall or independently prove the proposed mempool-fragmentation mechanism.
See [T10](#t10-decline-to-vote) and
[T27](#t27-mempool-partitioning-via-network-control).

**Historical implementation defects have identified fixes; re-verification is
partial.** T11 and T13 experiments on w34 demonstrated item-count handling
faults, connection disruption, and malformed-transaction process crashes. A w43
campaign re-tested invalid endorser blocks: every delivered attack EB was
rejected at the announcement, at decode, or at body arrival; none was endorsed;
and no crash occurred, so the w34 oversized-vector crash does not reproduce on
w43. The T13 malformed-transaction decoder crash has an identified upstream fix
that has not been re-verified on the current release. T12-related tests recorded
acceptance and memory retention of correctly signed votes for unknown targets,
and fixes remain unvalidated. These are version-specific findings requiring
closure evidence, not grounds to claim that the current release is vulnerable
or that these risks have been resolved. See [T11](#t11-create-invalid-eb),
[T12](#t12-create-invalid-vote), and
[T13](#t13-reference-invalid-transactions-in-eb).

**Duplicate submission costs are bounded.** On the w43 mixed devnet,
node-to-node duplicate handling was mitigated: a transaction identifier
re-announced twenty times on one connection, or offered once on each of three
concurrent connections, cost the receiver one body fetch and one validation.
Local resubmission pushed every duplicate through ledger validation before
rejection, about 0.15 ms each, with no amplification and no downstream
re-announcement. The tested attackers held a privileged position as the
receiver's local roots, and remote submission services were not measured. See
[T24](#t24-submit-duplicate-transactions).

**Within this assessment's scope, priority validation gaps include selective
data withholding and certified-data availability.** T21 requires validation of
certification availability when data is withheld from selected voters. T22 requires
evidence that delaying certified data to other honest nodes does not persistently
violate the timing assumptions on which Praos depends. Economic incentives,
censorship, and value extraction also require further analysis. The following
sections separate model mitigations from mitigations actually exercised.

## Threat status

The table summarizes assessment status, risk, and evidence for each threat. The
individual assessments describe the findings, tested conditions, and remaining
validation gaps.

| Threat # | Threat summary | Status | Risk | Evidence assessment |
|---|---|---|---|---|
| [T1](#t1-any-threat-to-praos) | Any threat to Praos | out of scope | — | No independent Praos assessment |
| [T2](#t2-vrf-grinding-on-eb-eligibility) | VRF grinding on EB eligibility | out of scope | — | Grinding resistance not assessed |
| [T3](#t3-vrf-grinding-on-voting-eligibility) | VRF grinding on voting eligibility | out of scope | — | Grinding resistance not assessed |
| [T4](#t4-vrf-key-compromise) | VRF key compromise | out of scope | — | Key compromise not assessed |
| [T5](#t5-eb-equivocation) | EB equivocation | prelim | Negative | Direct EB-equivocation coverage and resource impact unestablished |
| [T6](#t6-vote-equivocation) | Vote equivocation | TODO | — | Feasibility and scope unresolved |
| [T7](#t7-double-voting) | Double voting | TODO | — | No completed Haskell result |
| [T8](#t8-bls-key-compromise) | BLS key compromise | out of scope | — | Key theft and recovery not assessed |
| [T9](#t9-decline-to-create-eb) | Decline to create EB | final | Negative | Empirical confirmation pending |
| [T10](#t10-decline-to-vote) | Decline to vote | final | Negative | Praos continued during observed certification loss; incentives unvalidated |
| [T11](#t11-create-invalid-eb) | Create invalid EB | prelim | Negative | w43 campaign rejected all tested variants with no crash; w34 crash not reproduced; crypto-stage EB, non-empty size lie, and sustained flood untested |
| [T12](#t12-create-invalid-vote) | Create invalid vote | TODO | — | Historical unknown-target vote retention; full assessment pending |
| [T13](#t13-reference-invalid-transactions-in-eb) | Reference invalid transactions in EB | prelim | Positive | w34 committee-node crash via certified EB; upstream fix identified, not re-verified on w43 |
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
| [T24](#t24-submit-duplicate-transactions) | Submit duplicate transactions | final | Negative | Node-to-node deduplication mitigated; local resubmission costs one bounded validation per duplicate with no amplification; privileged position and remote services untested |
| [T25](#t25-submit-invalid-transactions) | Submit invalid transactions | prelim | Negative | No isolated real-node result established |
| [T26](#t26-submit-conflicting-transactions) | Submit conflicting transactions | in progress | — | Simulator inference; Haskell validation and resource cost pending |
| [T27](#t27-mempool-partitioning-via-network-control) | Mempool partitioning via network control | final | Positive | Recoverable certification disruption and substantial transaction delay in simulation; real-implementation partition validation pending |
| [T28](#t28-honeypot-contract-creating-transaction-races) | Honeypot contract creating transaction races | out of scope | — | Application economics not assessed |
| [T29](#t29-exploit-implementation-differences-between-node-versions) | Exploit implementation differences between node versions | out of scope | — | Adversarial mixed-version behavior not assessed |
| [T30](#t30-coordinate-governance-attacks-to-prevent-hard-fork) | Coordinate governance attacks to prevent hard fork | out of scope | — | Governance mitigations not assessed |
| [T31](#t31-honest-demand-exceeds-spo-storage-capabilities) | Honest demand exceeds SPO storage capabilities | out of scope | — | Long-term storage sustainability not assessed |
| [T32](#t32-silently-accumulate-bls-keys-to-forge-certificate) | Silently accumulate BLS keys to forge certificate | out of scope | — | Adaptive security and rotation effectiveness unresolved |
| [T33](#t33-silently-accumulate-vrf-keys-for-eligibility) | Silently accumulate VRF keys for eligibility | out of scope | — | Adaptive security and rotation effectiveness unvalidated |
| [T34](#t34-fork-to-extract-mev-from-a-recent-block) | Fork to extract MEV from a recent block | ? | — | Scope and feasibility pending; no mitigation validated |

**Legend:** Threat # = identifier in threat model version 0.5; EB = endorser
block; RB = ranking block; VRF = verifiable random function; BLS =
Boneh-Lynn-Shacham signature scheme; SPO = stake pool operator; MEV = maximal
extractable value. Status describes assessment progress: **final** = final
assessment; **prelim** = preliminary assessment; **in progress** = active
investigation; **TODO** = pending analysis, not started; **?** = pending
analysis of feasibility or scope; **out of scope** = excluded from this
assessment. Risk: **Negative** = no risk; **Positive** = risk identified; **—**
= risk not yet assessed. These labels do not grade severity. A negative
assessment applies to its evaluated conditions, not every variant,
implementation, or release. The evidence assessment identifies validation gaps
and historical failures that require follow-up, including those under threats
with a negative risk label.

## Threat assessments

### T1: Any threat to Praos

**Assessment.** Out of scope for a separate Praos assessment. This exclusion does
not remove the Leios-specific timing questions assessed under T21-T23 and T27.
No independent Praos security conclusion is made here. Source: [threat model](threat-model.md).

### T2: VRF grinding on EB eligibility

**Assessment.** Out of scope. Randomness
manipulation and grinding resistance require separate protocol and security
analysis. Neither grinding resistance nor the proposed
countermeasure was tested
here. Source: [threat model](threat-model.md).

### T3: VRF grinding on voting eligibility

**Assessment.** Out of scope. Randomness
manipulation and grinding resistance require separate protocol and security
analysis. No empirical or cryptographic validation of the
mitigation is claimed. Source: [threat model](threat-model.md).

### T4: VRF key compromise

**Assessment.** Out of scope. VRF cryptography and key custody have not been
assessed. Source: [threat model](threat-model.md).

### T5: EB equivocation

**Description.** A producer can distribute competing endorser-block announcements
to waste resources or divide voting. Exercising this threat requires production
eligibility, valid variant EBs, and ranking blocks announcing their different
hashes to different peers. A relay merely modifying another producer's EB body
creates a hash mismatch, not two valid competing announcements.

**Recommendation.** Exercise conflicting, valid EB announcements with controlled
peer delivery and record each honest node's detection, voting, and chain choice.
Measure resource use and throughput against a matched baseline.

**Assessment.** Preliminary. The mechanism is described above; direct
EB-equivocation validation and its resource impact remain unestablished.

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
implementation result has been established; mechanism analysis alone does not
validate Haskell vote accounting.

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

**Assessment.** Out of scope. T14 and T15 test certificate validation; they do not
establish resistance to theft of genuine keys. Source: [threat model](threat-model.md).

### T9: Decline to create EB

**Description.** An eligible producer omits an EB, reducing the additional
throughput available from Leios.

**Recommendation.** Document the tested conditions and observations. Distinguish
continued ranking-block production from lost EB throughput, and validate any
claimed economic deterrent separately.

**Assessment.** The negative risk assessment awaits empirical confirmation. The
effect on throughput and the effectiveness of economic deterrents remain to be
quantified.

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

**Assessment.** Base-chain operation continued at the observed moderate load
despite lost certification; it does not show that Leios throughput is unaffected
by missing quorum.

### T11: Create invalid EB

**Description.** A producer able to announce and serve adversarial EBs can target
byte limits, item limits, declared-size handling, duplicate manifests, or
malformed encodings at different processing stages.

**Evidence.** A w43 mixed-devnet campaign (23 November 2026) ran 13 fresh-devnet
runs across five variants — three per variant except malformed, which has one:
duplicate manifests (one valid transaction named twice); huge (100,000-entry,
roughly 3.8 MB) and oversized (13,889-entry, roughly 514 KB) manifests above
the devnet's 100,000-byte endorser-block size limit; hollow bodies (an empty
manifest announced with a false, larger declared size); and malformed CBOR
bodies. A roughly 20%-stake adversarial producer announced the invalid EBs on
the ranking blocks it forged against three Haskell nodes holding 80%
collectively. Every delivered attack EB was stopped before endorsement, at one
of three stages: at the announcement, where the header check rejected
above-limit EBs before any body fetch; at decoding, where an empty manifest
failed an item-count check and corrupted bodies failed CBOR decoding; or at
body arrival, where a post-decode check rejected duplicate transaction hashes.
All 36 duplicate-manifest EBs were rejected by every node that received them.
The one exception to clean rejection is the malformed-truncate corruption,
which breaks the outer message framing and stalls the fetch; it caused no harm
in its run and is tracked separately. No attack EB was validated, voted, or
certified; no crash or fatal error occurred; no link between two honest nodes
was torn down; and the three honest nodes finished every run on the same tip.

The single failing verdict, a chain-growth dip to 0.49 of baseline in one
oversized run, coincided with that run's host-load peak, did not reproduce in
the other runs, and is recorded as host-load noise rather than attack harm. All
runs ran under host load 28–76 from unrelated processes, which makes chain
growth the noisiest measurement in the set.

The w34 results are historical. The w34 oversized-vector crash — a stored
13,889-entry manifest overflowing a fixed 13,888-entry vector while being
served, stalling the chain — no longer reproduces on w43: the size and item
limits now sit in the header check, and the fetch buffers are derived from the
message limit rather than a fixed vector. The huge body that w34 rejected only
at the wire-size gate is now rejected at the announcement, before any fetch
begins, and the w34 size-mismatch disconnect for a declared-size lie is no
longer reached: a hollow body declared above the limit is rejected at the
announcement, and one declared below the limit is rejected at decoding because
an empty manifest is itself invalid. The duplicate-manifest experiment, first
filed under T24, is reclassified as the T11 duplicate variant, because
duplicates inside an EB require producer stake and make the EB itself invalid.

**Recommendation.** Exercise the untested stages: a decodable but
cryptographically invalid EB (bad VRF or body signature) and a declared-size lie
with a non-empty body below the header limit. Characterize the
malformed-truncate fetch stall and its cost under a sustained flood. Re-run the
boundary variants on a quiet host, run the malformed variant to the campaign's
three-run bar, and measure the reconnect churn that announcement-stage
rejections cause at higher adversarial stake or EB rates.

**Assessment.** Preliminary. On w43, all tested invalid-EB variants were
rejected before endorsement, with no crash and no honest-chain divergence, and
the w34 crash did not reproduce. The cryptographic rejection stage was never
reached, the truncate case stalls rather than rejects, sustained-flood resource
cost is unmeasured, and the malformed variant has fewer runs than the
campaign's own three-run integrity bar requires.

### T12: Create invalid vote

**Description.** Vote admission must check both cryptographic validity and target
context, while bounding retained state. A current committee-key holder can sign
fresh, arbitrary ranking-block hashes rather than replaying identical votes.

**Evidence.** A related w34 test against three local Haskell nodes submitted
such votes in batches small enough to pass the wire-size guard. Membership and
signature checks accepted them despite the unknown targets. One run grew from 12
to 129,012 acquired votes per node, with sampled memory rising from about 160 MB
to 310 MB and no observed reclaim during a 70-second post-test interval. These
observations suggest retained-state growth, but internal collection cardinality
was not measured and eventual exhaustion was not demonstrated. The nodes
survived. The recovery procedure calls for restarting affected nodes to release
accumulated state. Stopping the sender alone did not reclaim memory during the
measured interval. This is a semantic-admission and lifecycle finding, not
evidence of a bad signature passing verification.

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
to an honest ledger. The decoder crash has an identified upstream fix, merged on
17 September 2026; it has not been re-verified against the w43 release exercised
by the [T11](#t11-create-invalid-eb) campaign.

**Recommendation.** Use total transaction decoding and validation at the relevant
trust boundaries. Verify both rejection and process survival with confirmed
delivery, including restart conditions; separately verify honest ledger
non-application.

**Assessment.** Preliminary. The w34 dummy-transaction decoder crash has an
identified upstream fix that is not yet re-verified on a current release;
regression tests confirming rejection, process survival, and recovery remain
outstanding.

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

**Assessment.** The tested one-key/full-committee forgery was rejected. This is
an implementation check, not a proof of BLS cryptographic security or a test of
stolen quorum keys.

### T16: Omit targeted transactions from RB and EB

**Description.** A producer can delay selected transactions by omitting them.
The model expects honest mempool persistence and distributed production to limit
censorship, but even temporary delay can affect time-sensitive transactions.

**Recommendation.** Define the intended censorship duration, adversarial stake,
and workload, including deadline-sensitive transactions, before selecting an
experiment.

**Assessment.** Scope, feasibility, and risk remain to be assessed. Source:
[threat model](threat-model.md).

### T17: Reorder transactions in EB

**Description.** Reordering a fixed set of compatible, signed UTXO transactions 
within an endorser block preserves their economic outputs, provided the ordering 
remains valid.

**Assessment.** Closed by analysis: no independent value-extraction mechanism 
identified through transaction reordering alone. Scenarios requiring insertion, 
replacement, or exclusion of transactions belong under T18.

### T18: Insert or replace transactions in EB

**Description.** A producer may insert competing transactions or replace its
selected contents to capture value. Meaningful impact analysis requires actual
ledger constraints and application economics.

**Recommendation.** Construct a ledger-valid application scenario and measure
user loss and producer gain, including conflicts that prevent both transactions
from succeeding.

**Assessment.** In progress; conclusions remain pending. The availability of
transaction-injection tools does not establish an economic or implementation
result. Source: [threat model](threat-model.md).

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

**Assessment.** In progress; conclusions about the broader threat remain
pending. The negative historical mechanism experiment does not validate
incentive compatibility or the proposed mitigations. Source: [threat
model](threat-model.md).

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

**Assessment.** Preliminary. Retry behavior is a supported mitigation in the
modeled environment; real-node validation and throughput bounds remain open.

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

**Assessment.** Pending analysis. The proposed defenses have not been validated
against selective delivery to voting committee members.

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

**Assessment.** In progress. Neither the timing violation nor the effectiveness
of the proposed mitigation has been established.

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

**Assessment.** Preliminary. No harm was measured at this scale, and no released
EB was certified in the inspected log. Protection under sustained congestion
remains unverified.

### T24: Submit duplicate transactions

**Description.** A client can submit the same valid signed transaction
repeatedly through normal submission mechanisms to waste bandwidth and
processing. The threat model names no submission path, so both client paths to a
Haskell node were tested: node-to-node TxSubmission, which is pull-based (the
receiver asks for identifiers, then requests only bodies it does not already
hold), and local submission, the interface used by wallets and HTTP submission
services. Duplicates inside an endorser block require producer stake and make
the EB itself invalid; they are assessed under [T11](#t11-create-invalid-eb).

**Evidence.** Three fresh proto-devnet runs (23 November 2026, w43 Haskell
nodes) produced identical verdicts, with attacker-side and receiver-side
evidence recorded for every vector; only repeats made while the transaction was
in the receiver's mempool were counted. On the node-to-node path, a transaction
identifier announced 20 times on one connection, or offered once on each of
three concurrent connections, cost the receiver one body fetch and one
validation; downstream peers fetched the transaction once each, and no duplicate
caused a further downstream fetch. On the local path, every resubmission was
admitted to a full ledger-validation attempt and rejected there because the
first copy had already spent the inputs: one validation per duplicate, roughly
0.15 ms and 239 bytes each, so the receiver's work matched the attacker's bytes
with no amplification. Nothing was re-announced downstream. The attackers were
trustable local roots of the receiver, a privileged position; the unprivileged
node-to-node case, repeats within a single reply, remote HTTP submission
services, and sustained volume were not measured.

**Recommendation.** Repeat the measurement from an unprivileged network
position and against remote submission services, and test same-reply repeats and
sustained volume. A specified follow-on floods duplicate BLS key registrations,
whose proof-of-possession check spends receiver processor time rather than only
bandwidth; it has not been run. Rejection of malformed data must not be mistaken
for successful duplicate handling.

**Assessment.** Final for the tested proto-devnet scope. Node-to-node duplicate
handling is mitigated; local resubmission causes bounded, non-amplifying
validation waste.

### T25: Submit invalid transactions

**Description.** Invalid submissions test validation before propagation and the
cost of rejection. Random malformed bytes may stop at decoding; decodable but
invalid transactions are needed to exercise later validation stages. The tooling
distinguishes these cases, but their rejection costs have not been isolated in a
Haskell experiment. Ledger-less Rust clusters emulate validation and cannot
establish rejection before propagation. The EB-carried malformed-data findings
in [T13](#t13-reference-invalid-transactions-in-eb) exercise a different path
from transaction submission.

**Recommendation.** Isolate invalid submissions, verify which validation path
rejects them, and compare propagation and resource cost against a matched honest
load.

**Assessment.** Preliminary. Rejection before propagation and its resource cost
require isolated real-node validation.

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

**Evidence.** The final report (19 November 2026) consolidates the simulation
study; its measurements and qualifications supersede stronger interpretations in
the earlier per-run reports. The primary simulation used 2,685 nodes, seed 0, a
conflict-free 120 kB/s workload, and a complete bidirectional partition — 1,052
European nodes isolated from the other 1,633, cutting 84,746 directed edges —
during slots 300–700 of a 1,500-slot run. Neither side held the configured 75%
voting-stake threshold, so endorsements stalled: the count of blocks carrying
endorsements froze between slots 360 and 720 while the unpartitioned baseline
added seven, and endorsed transaction references held at 18,402 until counters
resumed after reconnection. Final results were a 97.58% block-inclusion proxy
against 97.71% without the partition (the proxy is not an independently verified
count of unique finalized transactions); 17 of 64 endorser blocks below the vote
threshold against 6 of 64 at baseline; whole-run mean transaction-to-block time
of 214.6 seconds against 84.1; and final mean pending-transaction age of 68.5
seconds against 16.5. Sampled mean pending age peaked at 427.1 seconds, and the
sampled mempool returned near baseline about 680 seconds after reconnection.
The similar endpoints conceal substantial delay: the whole-run latency average
includes partition-delayed transactions and does not isolate post-recovery
arrivals, so persistent slowdown for new transactions after recovery was not
established.

A higher-load run at 150 kB/s, isolated during slots 300–500, also drained its
backlog after reconnection (97.65% block-inclusion proxy), but without a matching
unpartitioned run at that load, capacity limits cannot be separated from
partition effects. An earlier partial cut of direct Europe–North America links
recorded a temporary voting drop and recovery, but no raw log is retained. The
conflicting-transaction run (10% conflict probability, longer partition) resumed
endorsements after reconnection; its limitations are described under
[T26](#t26-submit-conflicting-transactions). Earlier non-recovery observations
were attributed to an unimplemented simulator transaction-fetch path, not a
demonstrated protocol failure; the obsolete reports were removed and the
retained runs use the corrected path. These findings remain limited to one seed
and topology, partition windows of 200–600 seconds, and a simulator fetch path
not compared with the live node's implementation.

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
implementations. Extend simulation across seeds, topologies, and recurrent or
selective partitions; isolate transaction-load effects with controlled
comparisons. Record per-input finalized spends to directly check the inferred
single-spend behavior.

**Assessment.** Final report for the simulation phase. Complete regional
isolation temporarily stalled certification and caused substantial transaction
delay, with backlog drain after reconnection in the tested conflict-free runs;
the conflicting-transaction run resumed endorsements without independently
proving double-spend safety. Real-implementation partition validation, sustained
or repeated isolation, and mitigation effectiveness remain open.

### T28: Honeypot contract creating transaction races

**Assessment.** Out of scope. Generic conflicting-transaction tests do not establish
the economics or resource impact of such a contract.
Source: [threat model](threat-model.md).

### T29: Exploit implementation differences between node versions

**Assessment.** Out of scope. No cross-version safety conclusion is made by this
report. Source: [threat model](threat-model.md).

### T30: Coordinate governance attacks to prevent hard fork

**Assessment.** Out of scope. Network attack experiments do not validate these
social and organizational mitigations. Source: [threat model](threat-model.md).

### T31: Honest demand exceeds SPO storage capabilities

**Assessment.** Out of scope. Short attack runs and transient memory measurements
are not evidence of long-term storage sustainability.
Source: [threat model](threat-model.md).

### T32: Silently accumulate BLS keys to forge certificate

**Assessment.** Out of scope. The threat model explicitly leaves adaptive security
and rotation effectiveness for further research. T15 does not test this case:
a stolen quorum uses genuine signatures. Source: [threat model](threat-model.md).

### T33: Silently accumulate VRF keys for eligibility

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
| Coverage of agreed inventory | All T1-T34 entries assessed or explicitly marked pending or out of scope | Inventory coverage does not establish threat-model completeness |
| Certificate verification | All 27 delivered invalid-certificate blocks rejected on w38 | Remaining malformed encodings and contexts; resource cost and throughput under repeated attack; current-release regression evidence |
| Invalid data handling | Historical rejection, connection-fault, and process-crash observations; w43 campaign rejected all tested invalid-EB variants and the w34 crash did not reproduce | Re-verify the identified T13 decoder fix on the current release; crypto-stage EBs, non-empty-body size lies, truncate stalls, and sustained-flood costs |
| Vote admission and retention | Historical unknown-target acceptance and memory growth | Current target/context checks, bounded lifecycle, and recovery evidence |
| Withholding and diffusion | Rust-cluster retry experiments, burst tests, partition simulations | Realistic bandwidth and topology; certified-data availability to non-voters; validated diffusion allowance |
| Inaction and incentives | Praos continued during voting loss | Quantified throughput impact and evidence for economic deterrence |
| Censorship and value extraction | Model discussion and a narrower suppression experiment | Feasibility, application-value scenarios, and mitigation validation |
| Evidence completeness | Test conditions and outcomes summarized for completed experiments | Establish T9 and T25 results; complete fix-re-verification records for historical findings |

**Legend:** T1-T34 = the threat identifiers covered here; w38 = the prototype
release tested in the certificate experiments; w43 = the prototype release tested
in the invalid-EB and duplicate-submission campaigns; Praos = the underlying
Ouroboros chain-consensus protocol. "Delivered" means an attack block reached
honest-ledger validation. "Current-release" refers to the release selected for a
new validation campaign, not a claim that one was tested for this draft.

The immediate priorities are to re-verify historical invalid-data fixes on
current releases, complete the selective-withholding analysis, and validate
resource bounds and diffusion timing under realistic conditions. Economic and adaptive
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

This assessment combines experiments and mechanism analysis; the November 2026
update incorporates the w43 invalid-EB campaign, the duplicate-submission runs,
and the final T27 simulation report, without new experiments or independent
reanalysis of raw logs. Empirical conclusions
are limited to supported observations. Untested cases and missing measurements
remain unresolved regardless of the risk classification.

Prototype release labels do not establish the behavior of later builds. Closing
an implementation finding requires an identified fix and a regression that
confirms attack delivery, rejection, process survival, and recovery as applicable.
