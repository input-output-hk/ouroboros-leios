# Leios Assurance Report

This report is the companion to the [Leios requirements](./requirements.md). Where the requirements document states *what* must be demonstrated and mandates that every verification artefact cite the requirement identifiers it discharges, this report maintains the reverse index: for each requirement R1–R28, the artefacts that currently bear on it, the assurance route each provides, and an honest statement of how far the requirement is discharged.

This is a living document. It reflects the artefact landscape as first surveyed on 2026-09-08 and last revised on **2026-09-15**; it must be revised as artefacts land, are superseded, or are found wanting.

## Reading this report

- **Routes** follow the requirements document: **P** proof (Agda), **S** simulation/statistical analysis, **C** conformance (trace verification), **B** benchmark/prototype measurement, **T** test suite. **X** marks external or out-of-repo evidence (third-party reviews, field reports) that supports a route without being a project artefact in the sense of the requirements document.
- **Status** is per *clause*: each requirement is split in the matrix into the clauses its evidence divides along, and each clause is exactly one of:
    - **Discharged** — a current (Linear Leios, CIP-164) artefact establishes it, over stated parameter ranges.
    - **Open** — no discharging artefact yet; the artefact column states, *in italics*, what is needed (owner · size).
    - **Failing ⚠** — standing counter-evidence (live verification or audit) shows the prototype violating it; a tracked defect, with its work item named.
- A requirement's status is the worst of its clauses. There is no "partial": a clause either has its artefact or it does not.
- Artefacts are cited by the identifiers defined in the [Artefact index](#artefact-index). Pre-pivot (Short/Full Leios, input-block era) material is excluded as evidence and listed under [Excluded artefacts](#excluded-artefacts).

## The matrix

One table. Each requirement (bold row, with its proposed assurance routes) is split into numbered sub-items — the clauses its evidence divides along. Every sub-item is **Discharged**, **Open**, or **Failing ⚠**, and its last column names the artefact that satisfies it — or, where none exists, the artefact **needed**, with its natural owner (*spec* = formal spec and trace verifier, *sim* = simulation/analysis, *node* = node implementation, *infra* = CI/devnet/E2E) and size (**S** = days, **M** = 1–3 weeks, **L** = a month or more, or research-shaped). A requirement's status is the worst of its sub-items; nothing is "partially" satisfied. Gap entries — needed artefacts — are set in *italics*.

**Table 1 — Requirements, sub-items, and the artefacts that satisfy them.**

| # | Sub-item | Status | Artefact — satisfying, or needed (owner · size) |
|----|------------------------------|---------|-----------------------------------------------|
| **R1** | **RB diffusion keeps the Δ budget (5 s, ≥95% of stake) under maximal Leios load** [S, B] | | |
| R1.1 | — modelled | Open | *Needed: max-load campaign measuring RB time-to-≥95% against the 5 s budget at maximal Leios parameterisation (sim · M).* Groundwork: S-ATTACK, S-DQ. |
| R1.2 | — measured on hardware | Open | *Needed: devnet corroboration of R1.1 and R5.1 (infra · M).* Groundwork: B-ANTI. |
| **R2** | **EB transactions have the same ledger impact as RB transactions** [P, C, T] | | |
| R2.1 | obligation stated and proved | Open | *Needed: the EB≡RB obligation stated against the ledger interface (spec · M), then proved or reduced to documented ledger-spec properties (spec · L).* Context: X-LEDGER. |
| R2.2 | end-to-end equivalence test | Open | *Needed: E2E test applying the same transactions via EB and via RB and comparing ledger states (infra · M).* |
| **R3** | **Chain validity and selection unchanged** [P, C] | | |
| R3.1 | transfer theorems: CP/HCG/∃CQ reduce to Praos | Discharged | P-SAFETY, P-LIVE, P-INST (machine-checked). |
| R3.2 | the six instantiation hypotheses | Open | *Needed, all extending P-INST: `HashCorrectB` instantiated + `hash-unique` as a named collision-resistance assumption (spec · S); `isPure-Leios` (spec · M); `is-extension-eq` (spec · M); Praos-boundary decision + `IsBlockchain-base` (spec · M); `ChainLemma` — after R3.4, shares its machinery (spec · L); `SlotLemma` (spec · M).* |
| R3.3 | bare-node progress (non-vacuity) | Discharged | P-PROG. |
| R3.4 | composite-node progress | Open | *Needed: extend P-PROG through the network shim and base layer (spec · L).* |
| R3.5 | EBs/votes auxiliary in per-node behaviour | Discharged | C-VERIF. |
| **R4** | **Security constraints hold for the deployed parameterisation** [P, S, B] | | |
| R4.1 | certification deadline encoded normatively | Discharged | P-SPEC. |
| R4.2 | feasibility over the deployed parameter ranges | Open | *Needed: extend S-EBDIFF's sweeps to L_hdr, L_vote and L_diff, publishing the feasibility region (sim · M).* Groundwork: S-EBDIFF (one axis), S-PROB, S-CIP. |
| R4.3 | applying a certified EB cheaper than validating | Open | *Needed: apply-versus-validate benchmark on the prototype, alongside B-CRYPTO (node · M).* |
| **R5** | **No adversarial amplification lever against Praos** [S, B] | | |
| R5.1 | gigabyte-scale burst scenario executed | Open | *Needed: withheld-then-released burst campaign via `leios-tools`' eb-burst behaviour (T23), reporting the R1/R13 metrics under burst (sim · M); hardware corroboration rides R1.2.* |
| R5.2 | honest-cost-per-attacker-byte bound | Open | *Needed: cost accounting in the burst campaign (sim · M).* |
| R5.3 | implementation amplification channels closed | Open | X-AUDIT LEI-005/006/009/010/014 record resolutions. *Needed: verification of those resolutions — rides the R5.1/R1.2 runs.* |
| **R6** | **Sustain target throughput (140–300 TxkB/s)** [S, B] | | |
| R6.1 | in simulation on mainnet-like topology | Discharged | S-CIP, S-PROB. |
| R6.2 | sustained on SPO-grade hardware | Open | *Needed: a named SPO hardware specification (infra · S); a sustained ≥140 TxkB/s run on it, mainnet-like topology, mempool kept non-empty (infra · L).* Groundwork: B-ANTI (devnet only). |
| **R7** | **Honest nodes certify on quorum** [P, C, T] | | |
| R7.1 | rule normative in the spec | Discharged | P-SPEC. |
| R7.2 | implementation complies | Failing ⚠ | Counter-evidence: certificate famine (C-CHAIN, X-FIELD). *Needed: announcement-priority fix in the notification path (node · M), then re-measure inclusion rate against quorum availability with the chain verifier (spec · S).* |
| R7.3 | conformance cases target the rule | Open | *Needed: covered by the R12.4 generators and R12.5 instrumentation — no separate artefact.* |
| **R8** | **Graceful degradation, never below the Praos baseline** [S, B] | | |
| R8.1 | point studies of individual adversarial behaviours | Discharged | S-ATTACK, S-CAMP, S-EBDIFF. |
| R8.2 | degradation curve, Praos floor, recovery | Open | *Needed: sweep scenarios over adversarial stake in [0, 1−τ] (sim · S); the campaign publishing curve, floor and recovery time (sim · M).* |
| **R9** | **Latency bounded as percentiles, nominal and congested** [S, B, T] | | |
| R9.1 | nominal-load latency distribution | Discharged | S-LAT, S-DQ, B-ANTI. |
| R9.2 | congested-load percentiles | Open | *Needed: saturated-mempool scenario (sim · S); campaign publishing p50/p95/p99 alongside nominal (sim · M).* |
| **R10** | **Worst-case resource envelope sustainable on SPO-grade hardware** [B, S] | | |
| R10.1 | per-resource quantification | Discharged | B-COST, B-SQLITE, B-CRYPTO. |
| R10.2 | consolidated worst-case envelope vs a named spec | Open | *Needed: resource envelope recorded during the R6.2 run (infra · S); composition of the per-resource results into one worst-case table against the named specification (sim · M).* |
| R10.3 | disk growth boundable | Failing ⚠ | Counter-evidence: X-AUDIT LEI-008, unbounded LeiosDB retention. *Needed: bounded retention in the node (node · M).* |
| **R11** | **Certificate forgery infeasible below quorum τ** [P, S] | | |
| R11.1 | quorum statistics at surveyed committee sizes | Discharged | S-QUORUM. |
| R11.2 | bound at the deployed committee size and τ | Open | *Needed: extend S-QUORUM (`fiat-accompli.ipynb`) to the deployed point (sim · S).* |
| R11.3 | formal forgery reduction (BLS/PoP) | Open | *Needed: a new P module of named cryptographic assumptions — which BLS/proof-of-possession assumptions imply certificate soundness (spec · L).* Informal: X-CRYPTOREV. |
| R11.4 | certificate correctness tests | Discharged | B-CRYPTO. |
| **R12** | **Honest nodes vote exactly per the CIP-164 rules** [P, C, T] | | |
| R12.1 | voting rules normative | Discharged | P-SPEC. |
| R12.2 | live conformance instrument operating | Discharged | C-VERIF, C-EXTRACT, C-CHAIN. |
| R12.3 | node matches the deadline semantics | Failing ⚠ | Counter-evidence: two open divergences (X-FIELD; X-AUDIT LEI-012). *Needed: the deadline ruling — windowed (L_vote) vs point vs parameters — landed as a spec PR or node change (spec · M).* |
| R12.4 | property-based conformance coverage | Open | *Needed, extending C-EXTRACT: generators ported to Linear's nine actions (spec · M); negative generators keyed to the error taxonomy (spec · M); suite re-enabled in CI (spec · S).* |
| R12.5 | premise coverage known | Open | *Needed, extending C-VERIF: per-conjunct coverage instrumentation in `verifyStep` or a fold over `ValidTrace` (spec · M); report + baseline over the corpora (spec · S).* |
| **R13** | **Certified EB closure retrievable within L_diff at p99** [S, B] | | |
| R13.1 | analytic percentiles, conditional on certification | Discharged | S-EBDIFF, S-DQ. |
| R13.2 | measured p99 across honest nodes and certified EBs | Open | *Needed: per-certified-EB closure-completion instrumentation across nodes, extending B-ANTI's `analyse.py`, p99 stated against L_diff (infra · M).* |
| R13.3 | delivery path clear of known inefficiencies | Failing ⚠ | Counter-evidence: vote floods delay announcements; ~24× vote delivery (X-FIELD). *Needed: vote-delivery deduplication (node · M); the announcement-priority fix rides R7.2.* |
| **R14** | **Committee selection stake-proportional and manipulation-resistant** [P, S] | | |
| R14.1 | stake-proportionality statistics | Discharged | S-QUORUM. |
| R14.2 | at the deployed committee size and τ | Open | *Needed: the R11.2 artefact (shared).* |
| R14.3 | manipulation bound | Open | *Needed: grinding/manipulation model (stake-splitting, key-registration timing) with a quantified advantage bound, extending S-QUORUM (sim · L).* |
| **R15** | **Equivocation contained** [P, C, T] | | |
| R15.1 | rules in the spec | Open | *Needed: equivocation premises in the Linear spec — no vote for an equivocated EB, two-announcement cap, disconnection (spec · M).* |
| R15.2 | negative conformance tests | Open | *Needed: re-enable the disabled negative tests against the new rules (spec · S).* |
| R15.3 | implementation contains equivocation | Failing ⚠ | Counter-evidence: X-AUDIT LEI-011, equivocation does not prevent voting (resolution unverified). *Needed: node-level test via `leios-tools`' fake-EB behaviours (spec · M).* |
| **R16** | **Nodes acquire and serve every promptly-announced EB** [C, T] | | |
| R16.1 | serving/retention obligation in the spec | Open | *Needed: the obligation as spec premises or verifier side-conditions — FFD currently abstracts diffusion away (spec · M).* |
| R16.2 | verifier checks serving | Open | *Needed: C-CHAIN consuming the `EBSent` events C-SCHEMA already defines (spec · M).* |
| R16.3 | two-node serving test | Open | *Needed: integration test requesting EBs the SUT did not vote for and does not prefer (infra · M).* |
| **R17** | **Praos history rules apply to EB transactions** [T] | | |
| R17.1 | EB storage feasibility | Discharged | B-SQLITE. |
| R17.2 | sync-from-genesis over certified EBs | Open | *Needed: E2E sync-from-genesis suite (infra · L).* |
| **R18** | **Node-to-client interfaces: certified txs inlined, minimal client change** [T] | | |
| R18.1 | client-interface changes tested and documented | Open | *Needed: E2E client-interface checks — db-sync, Mithril, wallet-visible behaviour (infra · L).* Survey only: D-IMPACT. |
| **R19** | **Mixed-version network safe and live through the hard fork** [T] | | |
| R19.1 | transition tested | Open | *Needed: automated mixed-version upgrade suite (infra · L).* Planned in D-IMPACT. |
| **R20** | **Heterogeneous conforming implementations interoperate** [C, T] | | |
| R20.1 | implementation-neutral conformance instrument | Discharged | C-VERIF, D-NETSPEC. |
| R20.2 | interoperation demonstrated | Open | *Needed: a second implementation to test against; the R21.2 gate keeps the instrument neutral meanwhile.* |
| **R21** | **Implementations emit conforming execution traces** [T] | | |
| R21.1 | trace schema fixed and CI-validated | Discharged | C-SCHEMA. |
| R21.2 | node-emitted traces gated in CI | Open | *Needed, promoting C-CHAIN: `linear-chain` into the maintained `hs-src` tree (spec · S); a CI gate streaming testnet-harness node logs through it (infra · M); long-trace performance confirmed post-#1063 (spec · S).* |
| **R22** | **BLS keys generated and the certificate built offline** [T] | | |
| R22.1 | key pair and proof of possession generated offline | Open |  |
| R22.2 | registering certificate built in the same session | Open |  |
| **R23** | **BLS keys registered in a dedicated certificate** [T] | | |
| R23.1 | dedicated certificate exists | Open |  |
| R23.2 | the initial-release vehicle cannot change parameters silently | Open |  |
| **R24** | **Activation epoch known at submission, one active key per epoch** [C, T] | | |
| R24.1 | activation delay settled and applied deterministically | Open |  |
| R24.2 | one active BLS key per pool per epoch | Open |  |
| **R25** | **Node starts with both keys and changes over without a restart** [T] | | |
| R25.1 | node accepts both keys at startup | Open |  |
| R25.2 | no duty missed across the boundary | Open |  |
| **R26** | **Votes signed with the active BLS key, matched from chain state** [C, T] | | |
| R26.1 | selection rule follows chain state | Open |  |
| R26.2 | conformance evidence | Open |  |
| **R27** | **Key states and expiration epoch queryable** [T] | | |
| R27.1 | active key, next key and expiration epoch reported | Open |  |
| R27.2 | time-to-live margin stated for the deployed parameterisation | Open |  |
| **R28** | **Every non-voting condition named to the operator** [T] | | |
| R28.1 | invalid proof of possession surfaced | Open |  |
| R28.2 | pending, expired and missing keys surfaced | Open |  |

Across the 28 requirements: 70 sub-items — **18 discharged, 47 open, 5 failing**. At requirement level (worst sub-item): 0 discharged, 23 open, 5 failing (R7, R10, R12, R13, R15). The failing rows are the assurance machinery doing its job: each names its counter-evidence and its fix. The artefact column for R22 to R28 is not yet filled in.

The needed artefacts, tallied from Table 1:

**Table 2 — Needed artefacts by owner and size.**

| Owner | S | M | L | Total |
|-------|---|---|---|-------|
| spec | 7 | 13 | 4 | 24 |
| sim | 3 | 7 | 1 | 11 |
| node | 0 | 4 | 0 | 4 |
| infra | 2 | 5 | 4 | 11 |
| **All** | **12** | **29** | **9** | **50** |

Sequencing: within R3.2, the first item is independent and cheap, and `ChainLemma`/`SlotLemma` should follow R3.4, whose composite-trace machinery they need; the R6.2, R10.2 and R13.2 measurements ride one testnet campaign; several fixes are already in motion elsewhere (R10.3 is an audit resolution, R7.2/R13.3 are node-team findings already filed, R5.1's instrument merged 2026-09-14).

## Notes on the failing rows

- **R7.2 — certificate famine.** Vote floods through a single FIFO notification queue delay EB announcements, producing late-validation abstentions and skipped EBs at scale on the prototype devnet; found and measured by the live chain verifier (X-FIELD). The rule itself is sound in the spec; the fix is implementation-side.
- **R10.3 — unbounded retention.** X-AUDIT LEI-008: the SQLite LeiosDB grows without bound, so the disk-growth clause of R10 cannot currently be bounded at all.
- **R12.3 — deadline divergences.** The spec's point-in-time vote deadline versus the node's vote-when-validated behaviour, plus a sub-slot boundary mismatch (wall-clock node gates vs slot-granular spec); hundreds of datapoints per day from the field run, independently corroborated by X-AUDIT LEI-012. Whichever side moves, this is the process working: a ruling is owed, not just a fix.
- **R13.3 — delivery inefficiencies.** Announcements queue behind vote floods, and each vote is delivered roughly once per peer (~24×), eroding the diffusion budget the R13.1 model assumes available.
- **R15.3 — equivocation unchecked.** X-AUDIT LEI-011: observed announcement equivocation does not prevent voting. A spec-side gap first (the rule must exist before conformance can bind it) with the audit finding as standing counter-evidence.


## Artefact index

### P — formal proofs (repo: `ouroboros-leios-formal-spec`, dir `formal-spec/`)

The spec typechecks under `--safe` with no postulates or holes: what is proved is machine-checked. Module-level hypotheses are the caveat, not proof gaps.

**Table 3.**

| ID | Location | What it is |
|----|----------|------------|
| P-SPEC | `Leios/Linear.lagda.md` (+ `Leios/Protocol`, `Blocks`, `Voting`, `FFD`, `Base`, …) | The normative small-step relation for Linear Leios: slot, fetch, base-ledger and role rules; encodes voting rules and the certification deadline. Current (post-pivot). |
| P-SAFETY | `Blockchain/Safety.agda`, `Blockchain/Safety/Transfer.agda` | States Common Prefix; proves the generic safety-*transfer* theorem: a Leios-style extension inherits CP from its base chain. |
| P-LIVE | `Blockchain/Liveness.agda`, `Blockchain/Liveness/Transfer.agda` | States Honest Chain Growth and Existential Chain Quality; proves both transfer in each direction. |
| P-INST | `Network/Leios.agda` | Instantiates the transfer theorems for Linear Leios: `leiosSafety`, `leiosHCG`, `leios∃CQ`; proves RB-determines-EB injectivity. Parameterised on six unproved hypotheses (see caveats). |
| P-PROG | `Leios/Linear/Progress.agda` (branch `yveshauser/progress`, 2026-09-11 — cite the merged location once landed) | Progress proof for the bare Linear Leios node: from any state with completed slot upkeep, the node runs through a whole slot (`tick`), iterates (`ticks`), and reaches every future slot (`enough-traces`), for arbitrary delivered messages and ranking blocks. Establishes non-vacuity of the invariant-style safety/liveness statements; the composite-node (with network shim and base layer) lemma is stated as future work. |

### C — conformance

**Table 4.**

| ID | Location | What it is |
|----|----------|------------|
| C-VERIF | formal spec: `Leios/Linear/Trace/Verifier.lagda.md` (+ `Verifier/Test.lagda.md`) | Certified trace verifier: `verifyTrace` returns a correctness proof or a typed failure proof for any candidate execution trace. |
| C-EXTRACT | `leios-trace-verifier/` | MAlonzo-extracted Haskell verifier over simulator JSONL; golden corpus in `conformance-traces/` (5 valid, 2 invalid), Hspec runner, gated by `.github/workflows/conformance.yaml`. Property-based suite exists but is disabled (pre-pivot generators). |
| C-CHAIN | `leios-trace-verifier/dist/haskell/app/linear-chain/` | Live-node streaming verifier (`linear-leios-trace-verifier-chain`): reads node logs, queries leadership schedule and stake from a running node via `cardano-api`. The highest-value implementation-conformance instrument; currently only in the generated tree, not `hs-src`. |
| C-SCHEMA | `leios-trace-hs/`, `data/simulation/trace.haskell.schema.json` (+ config/topology schemas, CI validation) | Shared trace schema and parser guaranteeing simulators and verifier agree on the event language. |

### S — simulation and statistical analysis

The current Rust simulator lives out-of-repo (`input-output-hk/leios-tools`); campaign directories record the generating version in `sim-cli.hash` — provenance for every S citation below.

**Table 5.**

| ID | Location | What it is |
|----|----------|------------|
| S-CIP | `analysis/sims/cip/` | The parameter-justification campaign behind CIP-164's published values. |
| S-ATTACK | `analysis/sims/attack/` | Adversarial-scenario sweeps (report included). |
| S-CAMP | `analysis/sims/{degraded,2026w22-lazy-voter,bandwidth,params,micro-mainnet,pnsol,pnsol-praos,…}/` | Targeted Linear-era campaigns: degraded network, lazy voters, bandwidth, ΔQ cross-checks, Praos baseline. |
| S-PROB | `analysis/linear-leios-probabilities.ipynb` (+ throughput/efficiency analyses) | Certification/voting success probabilities and throughput curves for Linear Leios. |
| S-DQ | `analysis/deltaq/`, `delta_q/` | ΔQSD analytic diffusion model (tx lifecycle, preliminaries) with Haskell/Rust cross-comparison — latency bounds independent of the discrete-event simulator. |
| S-EBDIFF | `analysis/deltaq/improved-leios/` (merged to main via PR #1051, 2026-09-08) | Corrected and extended ΔQ model of EB-closure diffusion: discretised-CDF numerical backend, timing constants re-derived from empirical block data, Reno/Mathis vs CUBIC TCP congestion-control models bounding network sensitivity, S_EB-tx feasibility sweeps, certification probability under the CIP-164 stake-truncated committee, closure-diffusion CDF conditional on certification including partly Byzantine committees, Monte-Carlo tail validation. |
| S-QUORUM | `analysis/fiat-accompli.ipynb` (+ quorum and committee-statistics figures) | Fait-Accompli sortition and committee statistics: honest quorum reachable, adversarial quorum infeasible, by committee size. |
| S-LAT | `analysis/tx-to-block.ipynb` (+ figures) | Transaction-to-block inclusion latency. |
| S-BASE | `analysis/{stake_distribution,epoch-*}.…`, `data/internet/`, `data/BenchTopology/` | Empirical grounding: mainnet stake distribution and utilisation, real internet RTT dataset, measured topologies. |

### B — benchmarks and prototype measurement

**Table 6.**

| ID | Location | What it is |
|----|----------|------------|
| B-CRYPTO | `crypto-benchmarks.rs/` | Reference BLS voting/certificate implementation with Criterion benchmarks (vote, VRF, sortition, Fait-Accompli, serialisation) and correctness tests; CI-gated. Feeds the simulators' CPU model. |
| B-COST | `docs/cost-estimate/` | Per-resource operating-cost analysis (CPU, RAM, storage, egress, IOPS) with aggregate cost table, fee formula and TPS break-even. |
| B-SQLITE | `docs/targeted-design-investigations/microbenchmark-sqlite/` | Measured feasibility of EB storage on a relational store: closure/body query latency, index overhead, pruning, churn. |
| B-ANTI | `antithesis/` | Deterministic-simulation testing of the real `cardano-node-leios`: devnet under adversarial scheduling and fault injection, WAN emulation; computes cross-node liveness, TPS and latency metrics; CI-submitted. |

### T — test suites

Implementation test suites largely ride inside the artefacts above (C-EXTRACT's golden tests, B-CRYPTO's correctness tests, B-ANTI's metric-parser tests, the Haskell simulator's config/topology suite). No standalone T artefact currently discharges a requirement on its own; R17–R19 await the E2E and upgrade suites planned in D-IMPACT, and the artefacts for R22–R28 are not yet characterised.

### D — design and methodology documents (context, not evidence)

**Table 7.**

| ID | Location | What it is |
|----|----------|------------|
| D-IMPACT | `docs/ImpactAnalysis.md` | Per-area impact analysis; its "prototypes and experiments for derisking" and end-to-end-testing sections are the planned-artefact list for R17–R19. |
| D-DESIGN | `docs/leios-design/` | Design report; "Assumptions to validate early" and the risk analyses (data withholding, protocol bursts) are direct sources of future matrix rows. |
| D-FETCH | `docs/targeted-design-investigations/a-baseline-LeiosFetch-design/` | Baseline LeiosFetch and relational-storage design. |
| D-NETSPEC | `simulation/docs/network-spec/` | Mini-protocol network specification. |
| D-THREAT | `docs/threat-model.md`, `docs/mev/` | Threat model (current, post-pivot) and MEV research set for Linear Leios. |

### X — external and field evidence

**Table 8.**

| ID | Location | What it is |
|----|----------|------------|
| X-AUDIT | `audits/anastasia-labs-leios-audit-2026-09-01.pdf` | Third-party security audit (Anastasia Labs, v1.0, 2026-09-01) of the Leios consensus implementation: findings LEI-001–LEI-014, each with recommendation and resolution; publicly shareable per its disclosure statement. |
| X-CRYPTOREV | `docs/arc-voting-crypto-review.pdf` | External cryptographic review of the voting scheme. |
| X-PAPER | `docs/leiospaper-submitted.pdf` | The submitted Leios research paper (protocol security analysis). |
| X-FIELD | out-of-repo: `verifier-findings-report.md` (Taylor) | Field report: two-day (and continuing) live-node trace verification of a real Musashi block producer; nine findings with status, including the voting-deadline divergence (R12), certificate famine (R7) and tracer drift (R21). Should be brought into the repo or superseded by a repo artefact. |
| X-LEDGER | out-of-repo: `ledger-leios-inventory.md` (Taylor) | What the prototype's ledger integration actually implements, from pinned sources — descriptive input to R2. |

## Cross-cutting caveats

1. **The formal safety/liveness results are conditional transfer theorems.** P-SAFETY/P-LIVE prove that Leios *inherits* Common Prefix, Honest Chain Growth and Existential Chain Quality from Praos; P-INST applies them, but is module-parameterised on six unproved hypotheses (hash correctness and uniqueness, purity, the base chain being a blockchain, extension equality, and per-deployment Chain/Slot lemmas). Rows citing P-SAFETY/P-LIVE/P-INST are conditional until these are discharged. P-PROG removes the vacuity concern for the bare node (the trace sets the theorems quantify over are non-trivial); the composite-node progress lemma remains future work (R3.4). There is no absolute Leios safety proof, and no formal model of cryptographic hardness (BLS, VRF) anywhere in the P route.
2. **Property-based conformance is dark.** Only seven golden traces gate CI; the QuickCheck trace-generation suite is disabled pending its port from Short to Linear Leios. Until it returns, C evidence is thin for anything the golden traces do not touch.
3. **Live conformance is proven possible but not yet institutionalised.** C-CHAIN runs continuously against a real block producer (X-FIELD), but lives only in the generated tree, and no CI exercises node-emitted traces — the R21 drift can recur unnoticed between field runs.
4. **Simulator provenance is out-of-repo.** The current Rust simulator was extracted to `leios-tools`, which has since also grown a wire-level adversarial net-node with pluggable behaviours (eb-burst/T23, vote-flood, fake-EB variants) — the natural instrument for the R1/R5 campaigns and the R7.2/R13.3 fixes; S citations rest on each campaign's `sim-cli.hash`. The in-repo Haskell simulator is substantially pre-pivot (Short Leios core with a Linear variant layered on IB-shaped machinery) — usable for trace generation, weak as behavioural evidence.
5. **Composition rule.** Per the requirements' Notation: C artefacts carry weight only in composition with the P and S artefacts establishing that the specification itself satisfies the requirement. Several clauses discharged on the C route are P-conditional; they inherit caveat 1.

## Excluded artefacts

Pre-pivot (Short/Full Leios, input-block era) material is not cited as evidence: `docs/protocol-testing.md` and `docs/simulation-model-parameters.md` (IB-era test plans), `docs/technical-report-1.md` and `docs/Short-Pipeline Leios.md` (historical), the 2025 weekly campaigns under `analysis/sims/`, the Haskell simulator's scenario sets, `docs/obsolete-report/`, and the disabled property-based conformance generators. Where one of these is the only material near a clause, the clause is marked Open with no bearing artefacts.

## Maintenance

- When an artefact lands or changes, update its index entry and every requirement row citing it; every artefact must itself cite the requirement identifiers it discharges (requirements.md, Notation).
- A requirement is **Discharged** only when every sub-item is: each artefact current, stating its parameter ranges — including the hardware and percentile clauses where the requirement states them.
- ⚠ divergences are tracked defects: record the ruling (spec change, implementation change, or parameter change) and its artefact before clearing the flag.