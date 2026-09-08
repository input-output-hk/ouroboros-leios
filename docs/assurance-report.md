# Leios Assurance Report

This report is the companion to the [Leios requirements](./requirements.md). Where the requirements document states *what* must be demonstrated and mandates that every verification artefact cite the requirement identifiers it discharges, this report maintains the reverse index: for each requirement R1–R21, the artefacts that currently bear on it, the assurance route each provides, and an honest statement of how far the requirement is discharged.

This is a living document. It reflects the artefact landscape as surveyed on **2026-09-08** and must be revised as artefacts land, are superseded, or are found wanting.

## Reading this report

- **Routes** follow the requirements document: **P** proof (Agda), **S** simulation/statistical analysis, **C** conformance (trace verification), **B** benchmark/prototype measurement, **T** test suite. **X** marks external or out-of-repo evidence (third-party reviews, field reports) that supports a route without being a project artefact in the sense of the requirements document.
- **Status** per requirement:
    - **Discharged** — artefacts exist, are current (Linear Leios, CIP-164), state the parameter ranges over which they hold, and together cover the requirement.
    - **Partial** — relevant, current artefacts exist but with stated gaps: conditional on unproved assumptions, missing the mandated measurement (e.g. percentiles, SPO-grade hardware), or covering only part of the claim. Every Partial requirement's detail entry ends with a **Missing for discharge** enumeration: the specific artefacts or measurements that would move it to Discharged.
    - **Open** — no current artefact discharges any part of the requirement; anything listed is descriptive or planned.
- **⚠ divergence** flags a requirement where live evidence currently shows the prototype *violating* it — evidence that the assurance machinery works, and a tracked defect.
- Artefacts are cited by the identifiers defined in the [Artefact index](#artefact-index). Pre-pivot (Short/Full Leios, input-block era) material is excluded as evidence and listed under [Excluded artefacts](#excluded-artefacts).

## Summary matrix

| Req | Summary | Routes | Artefacts | Status |
|-----|---------|--------|-----------|--------|
| R1 | RB diffusion keeps the Δ budget under maximal Leios load | S, B | S-ATTACK, S-DQ, B-ANTI | Partial |
| R2 | EB transactions have the same ledger impact as RB transactions | P, C, T | X-LEDGER (descriptive only) | Open |
| R3 | Chain validity and selection unchanged | P, C | P-SAFETY, P-LIVE, P-INST, C-VERIF | Partial |
| R4 | Security constraints hold for deployed parameterisation | P, S, B | P-SPEC, S-PROB, S-CIP, S-EBDIFF, B-CRYPTO, B-COST | Partial |
| R5 | No adversarial amplification lever against Praos | S, B | S-ATTACK, B-ANTI, D-DESIGN, X-AUDIT | Partial |
| R6 | Sustain target throughput (140–300 TxkB/s) | S, B | S-CIP, S-PROB, S-EBDIFF, B-ANTI | Partial |
| R7 | Honest nodes certify on quorum | P, C, T | P-SPEC, C-CHAIN, X-FIELD | Partial ⚠ |
| R8 | Graceful degradation, never below Praos baseline | S, B | S-ATTACK, S-CAMP, S-EBDIFF | Partial |
| R9 | Latency bounded as percentiles, nominal and congested | S, B, T | S-LAT, S-DQ, B-ANTI | Partial |
| R10 | Worst-case resource envelope sustainable on SPO-grade hardware | B, S | B-COST, B-SQLITE, B-CRYPTO, X-AUDIT | Partial |
| R11 | Certificate forgery infeasible below quorum τ | P, S | S-QUORUM, B-CRYPTO, X-CRYPTOREV | Partial |
| R12 | Honest nodes vote exactly per CIP-164 rules | P, C, T | P-SPEC, C-VERIF, C-EXTRACT, C-CHAIN, X-FIELD, X-AUDIT | Partial ⚠ |
| R13 | Certified EB closure retrievable within L_diff at p99 | S, B | S-EBDIFF, S-DQ, S-CAMP, X-FIELD | Partial ⚠ |
| R14 | Committee selection stake-proportional, manipulation-resistant | P, S | S-QUORUM, B-CRYPTO | Partial |
| R15 | Equivocation contained | P, C, T | X-AUDIT (LEI-011) | Open |
| R16 | Nodes acquire and serve every promptly-announced EB | C, T | D-FETCH (design only) | Open |
| R17 | Praos history rules apply to EB transactions; sync from genesis | T | B-SQLITE (feasibility only) | Open |
| R18 | Node-to-client interfaces: certified txs inlined, minimal client change | T | D-IMPACT (survey only) | Open |
| R19 | Mixed-version network safe and live through the hard fork | T | D-IMPACT (planned suite) | Open |
| R20 | Heterogeneous conforming implementations interoperate | C, T | C-VERIF, D-NETSPEC (enabling only) | Open |
| R21 | Implementations emit conforming execution traces | T | C-SCHEMA, C-CHAIN, X-FIELD | Partial ⚠ |

No requirement is yet **Discharged**. That is expected at this stage: the requirements mandate parameter-range statements and hardware-grounded measurements that the artefact base does not yet make, and the strongest formal results are conditional (see [Cross-cutting caveats](#cross-cutting-caveats)).

## Per-requirement detail

### Preserve Praos persistence and liveness

**R1 — RB diffusion under maximal Leios traffic.** S-ATTACK sweeps adversarial and high-load scenarios; S-DQ bounds diffusion latency analytically and cross-checks Haskell/Rust implementations of the ΔQ model; B-ANTI runs a real `cardano-node-leios` devnet under adversarial scheduling. **Missing for discharge:** (1) a simulation campaign reporting the RB time-to-≥95 %-of-stake distribution with Leios at maximal parameterisation (S_EB-tx and vote traffic at their caps) on the mainnet-like topologies, stated against the 5 s budget; (2) the same measurement on real hardware (devnet or testnet) — no hardware measurement of RB diffusion under Leios load exists; (3) both stated over the deployed parameter ranges. The existing sims measure related quantities but never this one.

**R2 — EB transactions equivalent to RB transactions.** **Open.** The formal spec abstracts the base ledger, so no P artefact states this; no conformance or test artefact exercises it. X-LEDGER documents what the prototype's ledger integration actually implements (descriptive, not evidential). The natural discharge is a P obligation on the ledger-integration semantics plus end-to-end T evidence (D-IMPACT's planned E2E suite).

**R3 — Chain validity and selection unchanged.** The strongest formal results in the project: P-SAFETY and P-LIVE prove *transfer* theorems (if Praos satisfies Common Prefix / Honest Chain Growth / Existential Chain Quality, then Leios-as-extension does), and P-INST instantiates them for Linear Leios (`leiosSafety`, `leiosHCG`, `leios∃CQ`). C-VERIF checks per-node behaviour treats EBs/votes as auxiliary. **Missing for discharge:** proofs (or documented reductions to standard assumptions) for the six open hypotheses the instantiation is parameterised on — `HashCorrectB`, `hash-unique`, `isPure-Leios`, `IsBlockchain-base`, `is-extension-eq`, and the per-deployment Chain/Slot lemmas. Six obligations; none currently discharged.

**R4 — Security constraints for deployed parameterisation.** P-SPEC *encodes* the certification deadline (3L_hdr + L_vote + L_diff + (Δ_RB − Δ_applyTxs)) in its rules — normative, not demonstrative. S-PROB and S-CIP give the probabilistic evidence that deployable parameters meet it, and S-EBDIFF bounds the transmission-budget feasibility under two TCP congestion-control models; B-CRYPTO and B-COST bear on "applying a certified EB is cheaper than validating its transactions". **Missing for discharge:** (1) a stated feasibility region — which (L_hdr, L_vote, L_diff, S_EB-tx) tuples satisfy the transmission bound — locating the deployed values inside it with margin (S-EBDIFF sweeps one of the four axes; the other three are unswept); (2) a direct benchmark of apply-certified-EB cost versus validate-its-transactions cost — B-CRYPTO measures certificate verification only, and the EB-apply side has no measurement on any route.

**R5 — No amplification lever.** S-ATTACK covers adversarial sweeps; D-DESIGN analyses the withheld-then-released burst risk explicitly ("Protocol bursts"); B-ANTI is the platform on which a burst scenario can be executed against the real node. **Missing for discharge:** (1) an executed withheld-then-released burst scenario at the gigabyte scale the requirement names — reporting the R1 and R13 metrics under the burst — which has been run neither in simulation nor on B-ANTI; (2) a quantified bound on honest-node resource cost per attacker-supplied byte/EB: no artefact states this ratio. X-AUDIT bears directly on the resource-bounding clause at the implementation level: its ingress findings (LEI-005 unenforced body limits at Fetch ingress, LEI-006 future EB offers pinning global fetch state, LEI-009 attacker-controlled CBOR lengths driving allocation, LEI-010 first-seen offers poisoning the authoritative body size, LEI-014 unbudgeted signature verification on invalid vote batches) each identify an amplification channel, with resolutions recorded in the report.

### Deliver and sustain high throughput

**R6 — Target throughput.** S-CIP is the parameter-justification campaign behind CIP-164's 140–300 TxkB/s; S-PROB and the throughput/efficiency analyses chart sustained rates, and S-EBDIFF's S_EB-tx sweeps bound the maximum feasible closure size the network can carry. B-ANTI computes TPS on a real devnet. **Missing for discharge:** a sustained run at the target rate — at least the 140 TxkB/s floor, ideally the 300 TxkB/s ceiling — on mainnet-like topology and a *named* SPO-grade hardware specification, over a stated duration with the mempool kept non-empty. All current throughput evidence at target is simulation; the only hardware measurements (B-ANTI's devnet) claim neither mainnet-like topology nor SPO-grade hardware.

**R7 — Certify on quorum. ⚠** P-SPEC's rules require certificate inclusion when a quorum is seen; C-CHAIN checks it against a live node. **Live divergence:** the field run (X-FIELD and successors) currently shows a certificate famine on the prototype devnet — vote floods through a single FIFO notification queue delay EB announcements, producing `tooLate` abstentions and skipped EBs at scale. The requirement is being *tested* and is presently *failing* at the implementation level; tracked with the node team. **Missing for discharge:** (1) resolution of the certificate famine, evidenced by a devnet measurement showing the certificate-inclusion rate matching the quorum-availability rate within a stated tolerance; (2) dedicated conformance cases (golden and property-based) exercising the inclusion rule — the current golden corpus does not target it.

**R8 — Graceful degradation.** S-ATTACK plus the degraded-network and lazy-voter campaigns (S-CAMP) quantify throughput under adversarial inaction and network stress; S-EBDIFF quantifies certification and closure-diffusion degradation under a partly Byzantine committee. **Missing for discharge:** one analysis producing the full degradation curve — throughput as a function of adversarial committee-stake share over [0, 1−τ] — demonstrating all three clauses: the proportionality bound, the never-below-Praos floor, and recovery time once the adversarial condition ends. The existing campaigns are point studies of individual adversarial behaviours; none states the curve, the floor, or recovery.

**R9 — Latency percentiles.** S-LAT measures mempool-to-ledger inclusion latency; S-DQ models the tx lifecycle analytically; B-ANTI computes latency statistics on the devnet. **Missing for discharge:** stated percentiles (at minimum p50/p95/p99) for mempool-acceptance-to-ledger-inclusion latency under both nominal and congested (demand exceeding capacity) load, on the S route with B corroboration. S-LAT reports latency under nominal load only; congested-load percentiles exist on no route.

**R10 — Resource envelope.** The best-covered requirement. B-COST quantifies CPU, RAM, storage (including growth), egress and IOPS with a cost model and TPS break-even; B-SQLITE demonstrates EB storage feasibility on a relational store with measured query/prune/index costs; B-CRYPTO measures the CPU cost of voting, sortition and certificates. **Missing for discharge:** (1) the consolidated worst-case table — peak bandwidth, CPU, memory, IOPS and disk-growth rate at the target parameterisation — with each figure measured against a *named* SPO hardware specification, as the requirements' Notation demands; the per-resource pieces all exist but no artefact composes them, and none names the hardware it measured against; (2) resolution of X-AUDIT's LEI-008 (unbounded SQLite LeiosDB retention), without which the disk-growth clause is not boundable at all.

### Accept EBs only by distributed consensus

**R11 — Certificate soundness.** S-QUORUM analyses honest/adversarial quorum probabilities for the Fait-Accompli committee; B-CRYPTO's tests confirm certificates verify (and fail to verify) as intended; X-CRYPTOREV is the external review of the voting cryptography. **Missing for discharge:** (1) a formal statement of the forgery-infeasibility reduction — which BLS and proof-of-possession assumptions imply certificate soundness — currently absent from the P route entirely (the categorical-crypto framework composes machines but does not model hardness), leaving the claim resting on the external review and empirical tests; (2) the adversarial-quorum probability stated at the *deployed* committee size and τ — S-QUORUM charts committee sizes 500, 750 and 1000, but the deployed point and its bound are not stated.

**R12 — Voting rules. ⚠** P-SPEC's `VT-Role` rule is the normative statement; C-VERIF/C-EXTRACT check traces against it (accepting yields a machine-checked proof), and C-CHAIN does so against a live node with real leadership and stake queried from the node. **Live divergence:** the field run surfaced a genuine spec/implementation split — the spec's point-in-time vote deadline versus the node's vote-when-validated behaviour (hundreds of datapoints per day), plus a sub-slot deadline boundary (wall-clock node gates vs slot-granular spec). A ruling (windowed deadline vs parameters) is pending; whichever side moves, this is the assurance process working as intended. X-AUDIT independently corroborates deadline enforcement as the weak point from the security side (LEI-012: remote votes accepted after the voting deadline). **Missing for discharge:** (1) the deadline ruling and its matching change — a spec PR (windowed deadline expressed with L_vote) or a node change — closing both open divergences; (2) the QuickCheck trace-generator suite (`Spec.Generated`) ported from Short to Linear and re-enabled, replacing seven golden traces as the only CI conformance evidence; (3) per-premise coverage instrumentation in the verifier (per-conjunct counting in `verifyStep`, or a fold over the `ValidTrace` proof term), so it is known which of the voting rule's premises the traces actually exercise — none exists today.

**R13 — EB closure retrievable within L_diff. ⚠** S-EBDIFF is the strongest artefact here: it derives the full closure-diffusion CDF *conditional on certification* — the population the requirement quantifies over — under two TCP congestion-control models (Reno/Mathis and CUBIC) and a partly Byzantine committee, with Monte-Carlo tail validation, so stated percentiles can be read off analytically. S-DQ and the diffusion campaigns (S-CAMP) corroborate. **Live divergence:** field evidence shows announcement delivery delayed behind vote floods and each vote delivered ~24× (once per peer), both eroding the diffusion budget the model assumes available. **Missing for discharge:** (1) a measured per-EB closure-retrieval-time distribution across honest nodes at target S_EB-tx — instrument the devnet (extend `antithesis/analyse.py`, which already computes cross-node latency, with a per-certified-EB closure-completion metric) and state p99 against L_diff; no B-route artefact for this quantity exists; (2) the node fixes for the two delivery inefficiencies (announcement priority over vote floods in the notification path; vote-delivery deduplication), then re-measure.

**R14 — Committee selection.** S-QUORUM covers stake-proportionality and quorum statistics for persistent (Fait-Accompli) and sortition-based voters; B-CRYPTO benchmarks and tests the sortition implementation. **Missing for discharge:** (1) a manipulation analysis — an adversarial model of stake-splitting/key-registration grinding against Fait-Accompli persistent seats and sortition, with a quantified advantage bound (extend `fiat-accompli.ipynb` or a targeted design investigation); no artefact on any route addresses manipulation today; (2) the proportionality and quorum statistics restated at the deployed committee size and τ rather than the three surveyed sizes.

**R15 — Equivocation containment.** **Open.** The formal spec does not currently prohibit voting for an equivocated EB (the negative conformance tests for it are disabled), so there is no P statement to conform to; no C check or T case exercises the two-announcements limit or peer disconnection. X-AUDIT confirms the gap from the implementation side: LEI-011 finds that observed announcement equivocation does not prevent voting. This is a spec-side gap first — the rule must enter P-SPEC before C/T can bind the implementation to it — with the audit finding as the standing counter-evidence until then.

**R16 — Acquire and serve every announced EB.** **Open.** D-FETCH is a design for the fetch logic and relational storage — design, not evidence. No conformance check or test observes a node serving EBs it did not vote for or does not prefer.

**R17 — History rules for EB transactions.** **Open.** B-SQLITE shows storage feasibility only. Sync-from-genesis over certified EBs, indefinite retention, and serving to peers have no test; D-IMPACT plans the E2E suite that would carry this.

### Maintain compatible interfaces

**R18 — Node-to-client compatibility.** **Open.** D-IMPACT's ecosystem survey enumerates affected consumers (wallets, explorers, Mithril, db-sync) — a plan for evidence, not evidence.

**R19 — Hard-fork transition.** **Open.** D-IMPACT plans an automated upgrade-testing suite; nothing exists yet.

**R20 — Implementation interoperability.** **Open.** C-VERIF is the *instrument* that makes multi-implementation conformance possible (any implementation emitting conforming traces can be verified against the same spec), and D-NETSPEC specifies the mini-protocols; but with a single implementation today, interoperation cannot yet be demonstrated.

**R21 — Conforming execution traces. ⚠** C-SCHEMA fixes the trace format shared by simulators and verifier, with CI validation; C-CHAIN consumes real node logs. **Live divergence (resolved):** the field run found tracer-namespace drift had silently blinded the verifier to all Leios events — exactly the failure this requirement exists to prevent; fixed upstream with tests. **Missing for discharge:** (1) a CI gate that boots the local testnet harness (`testnet/` or the Antithesis devnet), streams node logs through C-CHAIN, and fails on nonconformance — today zero automated checks run on node-emitted traces (CI covers simulator traces only), so drift is detectable only by field runs; (2) `linear-chain` promoted from the generated tree into the maintained `hs-src` source tree so that gate has a supported instrument.

## Work items

The concrete things to make or do, consolidated from the Missing-for-discharge entries above and the Open requirements. Each names a deliverable and the requirements it moves.

| # | Route | Moves | Deliverable |
|---|-------|-------|-------------|
| W1 | P | R3 | Prove (or reduce to documented standard assumptions) the six open hypotheses in `Network/Leios.agda`: `HashCorrectB`, `hash-unique`, `isPure-Leios`, `IsBlockchain-base`, `is-extension-eq`, Chain/Slot lemmas. |
| W2 | P, T | R2 | State the EB-transactions-≡-RB-transactions obligation against the ledger rules and prove or reduce it; pair with an E2E test applying the same transaction set via EB and via RB and comparing resulting ledger states. |
| W3 | P, C | R15 | Add the equivocation rules to the Linear spec (no vote for an equivocated EB; at most two announcements per election; peer disconnection), then re-enable the disabled negative conformance tests against them. |
| W4 | C | R12 | Port the QuickCheck trace generators (`Spec.Generated` et al.) from Short to Linear and re-enable property-based conformance in CI. |
| W5 | C | R12, R7 | Per-premise (per-conjunct) coverage instrumentation in the verifier — per-arm counting in `verifyStep` or a fold over the `ValidTrace` proof term — reporting which rule premises the trace corpus exercises. |
| W6 | C | R21, R20 | CI gate: boot the local testnet harness, stream node logs through `linear-chain`, fail on nonconformance; promote `linear-chain` into the maintained `hs-src` tree. |
| W7 | S | R8 | One campaign sweeping adversarial committee-stake share over [0, 1−τ]: the full degradation curve, the Praos-baseline floor, and recovery time after the condition ends. |
| W8 | S | R9 | Congested-load latency campaign (mempool saturated): mempool-to-ledger p50/p95/p99, alongside the nominal-load figures. |
| W9 | S | R1, R5 | Max-load and withheld-then-released-burst campaigns measuring RB time-to-≥95 %-of-stake against the 5 s budget, with honest-cost-per-attacker-byte accounting in the burst case. |
| W10 | S | R11, R14 | Extend `fiat-accompli.ipynb`: adversarial-quorum bound at the deployed committee size and τ; a stake-splitting/grinding manipulation model with a quantified advantage bound. |
| W11 | B | R4 | Benchmark on the prototype: ledger-apply of a certified EB versus full validation of the same transactions. |
| W12 | B | R6, R13, R10 | Sustained devnet run at ≥140 TxkB/s on a named SPO-grade hardware spec; instrument per-certified-EB closure-completion times across nodes (extend `antithesis/analyse.py`) and state p99 against L_diff; record the resource envelope during the run. |
| W13 | B | R10 | Compose the per-resource results (B-COST, B-SQLITE, B-CRYPTO, W12) into one worst-case envelope table against a named SPO specification; resolve LEI-008 (bound LeiosDB retention). |
| W14 | impl | R7, R13 | Node fixes: announcement priority over vote floods in the notification path; vote-delivery deduplication; then re-measure certificate-inclusion rate against quorum availability. |
| W15 | T | R17, R18, R19 | Build the E2E suites planned in D-IMPACT: sync-from-genesis over certified EBs; client-interface checks (db-sync, Mithril, wallet-visible behaviour); automated mixed-version upgrade tests across the hard fork. |
| W16 | C, T | R16 | Conformance/integration checks that a node retains and serves every promptly-announced EB for the required window, including EBs it did not vote for and EBs on chains it does not prefer. |
| W17 | S, B | R4 | Extend the S-EBDIFF sweeps beyond S_EB-tx to the other three deadline parameters (L_hdr, L_vote, L_diff), publishing the feasibility region containing the deployed values. |

## Artefact index

### P — formal proofs (repo: `ouroboros-leios-formal-spec`, dir `formal-spec/`)

The spec typechecks under `--safe` with no postulates or holes: what is proved is machine-checked. Module-level hypotheses are the caveat, not proof gaps.

| ID | Location | What it is |
|----|----------|------------|
| P-SPEC | `Leios/Linear.lagda.md` (+ `Leios/Protocol`, `Blocks`, `Voting`, `FFD`, `Base`, …) | The normative small-step relation for Linear Leios: slot, fetch, base-ledger and role rules; encodes voting rules and the certification deadline. Current (post-pivot). |
| P-SAFETY | `Blockchain/Safety.agda`, `Blockchain/Safety/Transfer.agda` | States Common Prefix; proves the generic safety-*transfer* theorem: a Leios-style extension inherits CP from its base chain. |
| P-LIVE | `Blockchain/Liveness.agda`, `Blockchain/Liveness/Transfer.agda` | States Honest Chain Growth and Existential Chain Quality; proves both transfer in each direction. |
| P-INST | `Network/Leios.agda` | Instantiates the transfer theorems for Linear Leios: `leiosSafety`, `leiosHCG`, `leios∃CQ`; proves RB-determines-EB injectivity. Parameterised on six unproved hypotheses (see caveats). |

### C — conformance

| ID | Location | What it is |
|----|----------|------------|
| C-VERIF | formal spec: `Leios/Linear/Trace/Verifier.lagda.md` (+ `Verifier/Test.lagda.md`) | Certified trace verifier: `verifyTrace` returns a correctness proof or a typed failure proof for any candidate execution trace. |
| C-EXTRACT | `leios-trace-verifier/` | MAlonzo-extracted Haskell verifier over simulator JSONL; golden corpus in `conformance-traces/` (5 valid, 2 invalid), Hspec runner, gated by `.github/workflows/conformance.yaml`. Property-based suite exists but is disabled (pre-pivot generators). |
| C-CHAIN | `leios-trace-verifier/dist/haskell/app/linear-chain/` | Live-node streaming verifier (`linear-leios-trace-verifier-chain`): reads node logs, queries leadership schedule and stake from a running node via `cardano-api`. The highest-value implementation-conformance instrument; currently only in the generated tree, not `hs-src`. |
| C-SCHEMA | `leios-trace-hs/`, `data/simulation/trace.haskell.schema.json` (+ config/topology schemas, CI validation) | Shared trace schema and parser guaranteeing simulators and verifier agree on the event language. |

### S — simulation and statistical analysis

The current Rust simulator lives out-of-repo (`input-output-hk/leios-tools`); campaign directories record the generating version in `sim-cli.hash` — provenance for every S citation below.

| ID | Location | What it is |
|----|----------|------------|
| S-CIP | `analysis/sims/cip/` | The parameter-justification campaign behind CIP-164's published values. |
| S-ATTACK | `analysis/sims/attack/` | Adversarial-scenario sweeps (report included). |
| S-CAMP | `analysis/sims/{degraded,2026w22-lazy-voter,bandwidth,params,micro-mainnet,pnsol,pnsol-praos,…}/` | Targeted Linear-era campaigns: degraded network, lazy voters, bandwidth, ΔQ cross-checks, Praos baseline. |
| S-PROB | `analysis/linear-leios-probabilities.ipynb` (+ throughput/efficiency analyses) | Certification/voting success probabilities and throughput curves for Linear Leios. |
| S-DQ | `analysis/deltaq/`, `delta_q/` | ΔQSD analytic diffusion model (tx lifecycle, preliminaries) with Haskell/Rust cross-comparison — latency bounds independent of the discrete-event simulator. |
| S-EBDIFF | `analysis/deltaq/improved-leios/` (branch `yveshauser/deltaq-conditional-diffusion`, PR #1051 — cite the merged location once landed) | Corrected and extended ΔQ model of EB-closure diffusion: discretised-CDF numerical backend, timing constants re-derived from empirical block data, Reno/Mathis vs CUBIC TCP congestion-control models bounding network sensitivity, S_EB-tx feasibility sweeps, certification probability under the CIP-164 stake-truncated committee, closure-diffusion CDF conditional on certification including partly Byzantine committees, Monte-Carlo tail validation. |
| S-QUORUM | `analysis/fiat-accompli.ipynb` (+ quorum and committee-statistics figures) | Fait-Accompli sortition and committee statistics: honest quorum reachable, adversarial quorum infeasible, by committee size. |
| S-LAT | `analysis/tx-to-block.ipynb` (+ figures) | Transaction-to-block inclusion latency. |
| S-BASE | `analysis/{stake_distribution,epoch-*}.…`, `data/internet/`, `data/BenchTopology/` | Empirical grounding: mainnet stake distribution and utilisation, real internet RTT dataset, measured topologies. |

### B — benchmarks and prototype measurement

| ID | Location | What it is |
|----|----------|------------|
| B-CRYPTO | `crypto-benchmarks.rs/` | Reference BLS voting/certificate implementation with Criterion benchmarks (vote, VRF, sortition, Fait-Accompli, serialisation) and correctness tests; CI-gated. Feeds the simulators' CPU model. |
| B-COST | `docs/cost-estimate/` | Per-resource operating-cost analysis (CPU, RAM, storage, egress, IOPS) with aggregate cost table, fee formula and TPS break-even. |
| B-SQLITE | `docs/targeted-design-investigations/microbenchmark-sqlite/` | Measured feasibility of EB storage on a relational store: closure/body query latency, index overhead, pruning, churn. |
| B-ANTI | `antithesis/` | Deterministic-simulation testing of the real `cardano-node-leios`: devnet under adversarial scheduling and fault injection, WAN emulation; computes cross-node liveness, TPS and latency metrics; CI-submitted. |

### T — test suites

Implementation test suites largely ride inside the artefacts above (C-EXTRACT's golden tests, B-CRYPTO's correctness tests, B-ANTI's metric-parser tests, the Haskell simulator's config/topology suite). No standalone T artefact currently discharges a requirement on its own; R17–R19 await the E2E and upgrade suites planned in D-IMPACT.

### D — design and methodology documents (context, not evidence)

| ID | Location | What it is |
|----|----------|------------|
| D-IMPACT | `docs/ImpactAnalysis.md` | Per-area impact analysis; its "prototypes and experiments for derisking" and end-to-end-testing sections are the planned-artefact list for R17–R19. |
| D-DESIGN | `docs/leios-design/` | Design report; "Assumptions to validate early" and the risk analyses (data withholding, protocol bursts) are direct sources of future matrix rows. |
| D-FETCH | `docs/targeted-design-investigations/a-baseline-LeiosFetch-design/` | Baseline LeiosFetch and relational-storage design. |
| D-NETSPEC | `simulation/docs/network-spec/` | Mini-protocol network specification. |
| D-THREAT | `docs/threat-model.md`, `docs/mev/` | Threat model (current, post-pivot) and MEV research set for Linear Leios. |

### X — external and field evidence

| ID | Location | What it is |
|----|----------|------------|
| X-AUDIT | `audits/anastasia-labs-leios-audit-2026-09-01.pdf` | Third-party security audit (Anastasia Labs, v1.0, 2026-09-01) of the Leios consensus implementation: findings LEI-001–LEI-014, each with recommendation and resolution; publicly shareable per its disclosure statement. |
| X-CRYPTOREV | `docs/arc-voting-crypto-review.pdf` | External cryptographic review of the voting scheme. |
| X-PAPER | `docs/leiospaper-submitted.pdf` | The submitted Leios research paper (protocol security analysis). |
| X-FIELD | out-of-repo: `verifier-findings-report.md` (Taylor) | Field report: two-day (and continuing) live-node trace verification of a real Musashi block producer; nine findings with status, including the voting-deadline divergence (R12), certificate famine (R7) and tracer drift (R21). Should be brought into the repo or superseded by a repo artefact. |
| X-LEDGER | out-of-repo: `ledger-leios-inventory.md` (Taylor) | What the prototype's ledger integration actually implements, from pinned sources — descriptive input to R2. |

## Cross-cutting caveats

1. **The formal safety/liveness results are conditional transfer theorems.** P-SAFETY/P-LIVE prove that Leios *inherits* Common Prefix, Honest Chain Growth and Existential Chain Quality from Praos; P-INST applies them, but is module-parameterised on six unproved hypotheses (hash correctness and uniqueness, purity, the base chain being a blockchain, extension equality, and per-deployment Chain/Slot lemmas). Rows citing P-SAFETY/P-LIVE/P-INST are conditional until these are discharged. There is no absolute Leios safety proof, and no formal model of cryptographic hardness (BLS, VRF) anywhere in the P route.
2. **Property-based conformance is dark.** Only seven golden traces gate CI; the QuickCheck trace-generation suite is disabled pending its port from Short to Linear Leios. Until it returns, C evidence is thin for anything the golden traces do not touch.
3. **Live conformance is proven possible but not yet institutionalised.** C-CHAIN runs continuously against a real block producer (X-FIELD), but lives only in the generated tree, and no CI exercises node-emitted traces — the R21 drift can recur unnoticed between field runs.
4. **Simulator provenance is out-of-repo.** The current Rust simulator was extracted to `leios-tools`; S citations rest on each campaign's `sim-cli.hash`. The in-repo Haskell simulator is substantially pre-pivot (Short Leios core with a Linear variant layered on IB-shaped machinery) — usable for trace generation, weak as behavioural evidence.
5. **Composition rule.** Per the requirements' Notation: C artefacts carry weight only in composition with the P and S artefacts establishing that the specification itself satisfies the requirement. Several Partial rows above are C-strong but P-conditional; they inherit caveat 1.

## Excluded artefacts

Pre-pivot (Short/Full Leios, input-block era) material is not cited as evidence: `docs/protocol-testing.md` and `docs/simulation-model-parameters.md` (IB-era test plans), `docs/technical-report-1.md` and `docs/Short-Pipeline Leios.md` (historical), the 2025 weekly campaigns under `analysis/sims/`, the Haskell simulator's scenario sets, `docs/obsolete-report/`, and the disabled property-based conformance generators. Where one of these is the only material near a requirement, the requirement is marked Open, not Partial.

## Maintenance

- When an artefact lands or changes, update its index entry and every requirement row citing it; every artefact must itself cite the requirement identifiers it discharges (requirements.md, Notation).
- A requirement moves to **Discharged** only when its artefacts are current, state their parameter ranges, and jointly cover the full claim — including the hardware and percentile clauses where the requirement states them.
- ⚠ divergences are tracked defects: record the ruling (spec change, implementation change, or parameter change) and its artefact before clearing the flag.
