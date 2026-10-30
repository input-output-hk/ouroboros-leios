# Leios Assurance Report

This report is the companion to the [Leios requirements](./requirements.md). Where the requirements document states *what* must be demonstrated and mandates that every verification artefact cite the requirement identifiers it discharges, this report maintains the reverse index: for each requirement R1–R28, the artefacts that currently bear on it, the assurance route each provides, and an honest statement of how far the requirement is discharged.

This is a living document. It reflects the artefact landscape as first surveyed on 2026-09-08 and last revised on **2026-10-06**; it must be revised as artefacts land, are superseded, or are found wanting.

## Reading this report

- **Routes** follow the requirements document: **P** proof (Agda), **S** simulation/statistical analysis, **C** conformance (trace verification), **B** benchmark/prototype measurement, **T** test suite. **X** marks external or out-of-repo evidence (third-party reviews, field reports) that supports a route without being a project artefact in the sense of the requirements document.
- **Status** is per *clause*: each requirement is split in the matrix into the clauses its evidence divides along, and each clause is exactly one of:
    - **Discharged** — a current (Linear Leios, CIP-164) artefact establishes it, over stated parameter ranges.
    - **Open** — no discharging artefact yet; the artefact column states, *in italics*, what is needed (owner · size).
    - **Failing ⚠** — standing counter-evidence (live verification, an audit finding, or a defect the node team has itself filed) shows the prototype violating it; a tracked defect, with its fix named.
- A requirement's status is the worst of its clauses. There is no "partial": a clause either has its artefact or it does not.
- Artefacts are cited by the identifiers defined in the [Artefact index](#artefact-index). Pre-pivot (Short/Full Leios, input-block era) material is excluded as evidence and listed under [Excluded artefacts](#excluded-artefacts).

## The matrix

One table. Each requirement (bold row, with its proposed assurance routes) is split into numbered sub-items — the clauses its evidence divides along. Every sub-item is **Discharged**, **Open**, or **Failing ⚠**, and its last column names the artefact that satisfies it — or, where none exists, the artefact **needed**, with its natural owner (*spec* = formal spec and trace verifier, *sim* = simulation/analysis, *node* = node implementation, *ledger* = cardano-ledger and its formal specification, *infra* = CI/devnet/E2E, *docs* = operator documentation) and size (**S** = days, **M** = 1–3 weeks, **L** = a month or more, or research-shaped). A requirement's status is the worst of its sub-items; nothing is "partially" satisfied. Gap entries — needed artefacts — are set in *italics*.

**Table 1 — Requirements, sub-items, and the artefacts that satisfy them.**

| # | Sub-item | Status | Artefact — satisfying, or needed (owner · size) |
|----|------------------------------|---------|-----------------------------------------------|
| **R1** | **RB diffusion keeps the Δ budget (5 s, ≥95% of stake) under maximal Leios load** [S, B] | | |
| R1.1 | — modelled | Open | *Needed: max-load campaign measuring RB time-to-≥95% against the 5 s budget at maximal Leios parameterisation (sim · M).* Groundwork: S-ATTACK, S-DQ. |
| R1.2 | — measured on hardware | Open | *Needed: devnet corroboration of R1.1 and R5.1 (infra · M).* Groundwork: B-ANTI, B-DEVNET, B-BURST. Caution: the relay inbound-governor wedge seen on w38–w39 (X-FIELD) must be fixed first — the cherry-pick of ouroboros-network `1ccd17298` — or a devnet run cannot be read as evidence. |
| **R2** | **EB transactions have the same ledger impact as RB transactions** [P, C, T] | | |
| R2.1 | obligation stated and proved | Open | Groundwork: P-LLF — `ValidEB`'s valid-extension conjunct runs an EB's transactions through the same `LEDGERS` rule as a block's (formal-ledger-specifications #1330); the `CHAIN` rule that applies a certified EB is in flight (#1346). *Needed: once that rule lands, EB≡RB stated as a lemma over `LEDGERS` (spec · M), then proved or reduced to documented ledger-spec properties (spec · L).* Context: X-LEDGER. |
| R2.2 | end-to-end equivalence test | Open | *Needed: E2E test applying the same transactions via EB and via RB and comparing ledger states (infra · M).* Groundwork: B-SYNTH forges chains whose blocks and EBs carry the same respending transaction stream. |
| **R3** | **Chain validity and selection unchanged** [P, C] | | |
| R3.1 | transfer theorems: CP/HCG/∃CQ reduce to Praos | Discharged | P-SAFETY, P-LIVE, P-INST (machine-checked). |
| R3.2 | the remaining instantiation hypotheses | Open | `is-extension-eq` is gone: the protocol correspondence is now a machine isomorphism and `ChannelCat`'s inconsistent assumptions were removed (spec PR #71). *Needed, all extending P-INST: `HashCorrectB` instantiated + `hash-unique` as a named collision-resistance assumption (spec · S); `isPure-Leios` (spec · M); Praos-boundary decision + `IsBlockchain-base` (spec · M); `ChainLemma` and `SlotLemma` — in flight as spec PR #75, which answers chain and slot queries through a query port rather than the cached chain (spec · L).* |
| R3.3 | bare-node progress (non-vacuity) | Discharged | P-PROG (merged 2026-09-15). |
| R3.4 | composite-node progress | Open | *Needed: extend P-PROG through the network shim and base layer (spec · L).* In flight: spec PR #72 (every shim message answered; the composite node completes a slot). |
| R3.5 | EBs/votes auxiliary in per-node behaviour | Discharged | C-VERIF. |
| **R4** | **Security constraints hold for the deployed parameterisation** [P, S, B] | | |
| R4.1 | certification deadline encoded normatively | Discharged | P-SPEC. |
| R4.2 | feasibility over the deployed parameter ranges | Open | *Needed: extend S-EBDIFF's sweeps to L_hdr, L_vote and L_diff, publishing the feasibility region (sim · M).* Groundwork: S-EBDIFF (one axis), S-PROB, S-CIP. |
| R4.3 | applying a certified EB cheaper than validating | Open | *Needed: apply-versus-validate benchmark on the prototype, alongside B-CRYPTO (node · M).* Groundwork: S-POSTCIP's `apply-reapply` regression of mainnet `db-analyser` data, the ledger-level cost gap between `Apply` and `Reapply`. |
| **R5** | **No adversarial amplification lever against Praos** [S, B] | | |
| R5.1 | gigabyte-scale burst scenario executed | Open | *Needed: withheld-then-released burst campaign via `leios-tools`' eb-burst behaviour (T23), reporting the R1/R13 metrics under burst (sim · M); hardware corroboration rides R1.2.* Groundwork: X-ADV T23 — bursts of twenty and a hundred real EBs on a devnet did no measurable harm and none of the stale EBs certified, far below the scale R5 names; B-BURST is the hardware instrument. |
| R5.2 | honest-cost-per-attacker-byte bound | Open | *Needed: cost accounting in the burst campaign (sim · M).* |
| R5.3 | implementation amplification channels closed | Failing ⚠ | X-AUDIT LEI-004/005/009 closed by consensus #2358 (prototype-2026w40, D-CHANGELOG): fixed-width hashes, every declared count checked before allocation; LEI-006/010/014 record resolutions. Counter-evidence: the vote state grew without bound, and because a vote carries no slot an adversary can evict honest tallies with fabricated votes on invented RB hashes, each costing a BLS verification before anything can refuse it (consensus #2367, a node-team finding; its 128-point bound is declared unsafe). *Needed: a slot in the vote, so a late or far vote is refused before it occupies anything (node · M); verification of the LEI resolutions rides the R5.1/R1.2 runs.* |
| **R6** | **Sustain target throughput (140–300 TxkB/s)** [S, B] | | |
| R6.1 | in simulation on mainnet-like topology | Discharged | S-CIP, S-PROB. |
| R6.2 | sustained on SPO-grade hardware | Open | *Needed: a named SPO hardware specification (infra · S); a sustained ≥140 TxkB/s run on it, mainnet-like topology, mempool kept non-empty (infra · L).* Groundwork: B-ANTI, B-DEVNET (devnets, not SPO hardware). |
| **R7** | **Honest nodes certify on quorum** [P, C, T] | | |
| R7.1 | rule normative in the spec | Discharged | P-SPEC. |
| R7.2 | implementation complies | Failing ⚠ | Counter-evidence: certificate famine (C-CHAIN, X-FIELD), still live on prototype-2026w38a — the field verifier ends a session on a missed or late vote every few minutes (2026-10-06); X-FIELD's announcement-path finding locates the cause (the kernel ignores the chain's copy of the announcement and waits for gossip through one FIFO). *Needed: announcement-priority fix in the notification path (node · M), then re-measure inclusion rate against quorum availability with the chain verifier (spec · S).* |
| R7.3 | conformance cases target the rule | Discharged | C-VERIF: the verifier decides the certificate steps `Cert₁`–`Cert₃` from their generated premises, and `Verifier/Test.lagda.md` exercises the certificate firing, the tip moving under an outstanding query, and rejects broken certificate steps (spec PR #61). The R12.4 generators will widen this. |
| **R8** | **Graceful degradation, never below the Praos baseline** [S, B] | | |
| R8.1 | point studies of individual adversarial behaviours | Discharged | S-ATTACK, S-CAMP, S-EBDIFF. |
| R8.2 | degradation curve, Praos floor, recovery | Open | *Needed: sweep scenarios over adversarial stake in [0, 1−τ] (sim · S); the campaign publishing curve, floor and recovery time (sim · M).* |
| **R9** | **Latency bounded as percentiles, nominal and congested** [S, B, T] | | |
| R9.1 | nominal-load latency distribution | Discharged | S-LAT, S-DQ, B-ANTI. |
| R9.2 | congested-load percentiles | Open | *Needed: saturated-mempool scenario (sim · S); campaign publishing p50/p95/p99 alongside nominal (sim · M).* |
| **R10** | **Worst-case resource envelope sustainable on SPO-grade hardware** [B, S] | | |
| R10.1 | per-resource quantification | Discharged | B-COST, B-SQLITE, B-CRYPTO. |
| R10.2 | consolidated worst-case envelope vs a named spec | Open | *Needed: resource envelope recorded during the R6.2 run (infra · S); composition of the per-resource results into one worst-case table against the named specification (sim · M).* |
| R10.3 | disk growth boundable | Open | Counter-evidence resolved: the LeiosDB is now a volatile and an immutable partition, with mark-and-sweep garbage collection of the volatile side (consensus #2261, prototype-2026w38) — LEI-008's no-op lifecycle hooks are gone; the immutable side is chain history and grows with it (R17). The w40 schema stores a transaction once per EB that references it, trading disk for write speed (consensus #2334). Instrument: B-DEVNET's LeiosDB dashboard and the partition-size node metrics (cardano-node #6656). *Needed: a measured run showing `leios.vol.db` bounded and `leios.imm.db` growing at the chain's rate (infra · S).* |
| **R11** | **Certificate forgery infeasible below quorum τ** [P, S] | | |
| R11.1 | quorum statistics at surveyed committee sizes | Discharged | S-QUORUM. |
| R11.2 | bound at the deployed committee size and τ | Open | *Needed: extend S-QUORUM (`fiat-accompli.ipynb`) to the deployed point (sim · S).* |
| R11.3 | formal forgery reduction (BLS/PoP) | Open | Groundwork: P-VOTE proves the quorum half — a certificate implies `threshold` distinct valid votes, hence an honest validator whenever fewer than `threshold` parties are corrupt — and the real scheme refines the ideal one. *Needed: P-VOTE's `Valid` predicate instantiated by BLS aggregate verification under named cryptographic assumptions (spec · L).* Informal: X-CRYPTOREV. In flight: P-LLF `ValidEBCert` (#1333). |
| R11.4 | certificate correctness tests | Discharged | B-CRYPTO; X-ADV T15 — forged certificates with a one-key aggregate over a full-committee bitfield, on three fresh devnets, every one rejected by the ledger's `verifyLeiosCert`. |
| **R12** | **Honest nodes vote exactly per the CIP-164 rules** [P, C, T] | | |
| R12.1 | voting rules normative | Discharged | P-SPEC, P-VOTE (`VT-Defer`: a node that can vote must have voted by `voteDeadline = t + 3·L_hdr + L_vote`). |
| R12.2 | live conformance instrument operating | Discharged | C-VERIF, C-EXTRACT, C-CHAIN. |
| R12.3 | node matches the deadline semantics | Failing ⚠ | The spec has ruled: the deadline is a window (`VT-Defer`, P-VOTE). Counter-evidence remains on the node side: receipt freshness `recv = eb+2` against `L_hdr = 1` on every field-verifier session since the w38a rebuild (X-FIELD, 2026-09-24, unchanged on 2026-10-06); and remote votes accepted after the deadline because a vote carries no slot (X-AUDIT LEI-012, unresolved — the same defect R5.3 names). *Needed: the node change — a slot in the vote and one admission predicate for local and remote votes (node · M); then re-measure with C-CHAIN (spec · S).* |
| R12.4 | property-based conformance coverage | Open | *Needed, extending C-EXTRACT: generators ported to Linear's nine actions (spec · M); negative generators keyed to the error taxonomy (spec · M); suite re-enabled in CI (spec · S).* |
| R12.5 | premise coverage known | Open | *Needed, extending C-VERIF: per-conjunct coverage instrumentation in `verifyStep` or a fold over `ValidTrace` (spec · M); report + baseline over the corpora (spec · S).* |
| **R13** | **Certified EB closure retrievable within L_diff at p99** [S, B] | | |
| R13.1 | analytic percentiles, conditional on certification | Discharged | S-EBDIFF, S-DQ. |
| R13.2 | measured p99 across honest nodes and certified EBs | Open | *Needed: per-certified-EB closure-completion instrumentation across nodes, extending B-ANTI's `analyse.py`, p99 stated against L_diff (infra · M).* Groundwork: B-DEVNET's diffusion dashboard (ouroboros-leios #1096); EB-diffusion measurement in #1102 (open). |
| R13.3 | delivery path clear of known inefficiencies | Failing ⚠ | Counter-evidence: vote floods delay announcements; ~24× vote delivery (X-FIELD). LeiosNotify now pipelines a thousand requests (consensus #2366) — a stress-test setting, not the fix. *Needed: vote-delivery deduplication (node · M); the announcement-priority fix rides R7.2.* |
| **R14** | **Committee selection stake-proportional and manipulation-resistant** [P, S] | | |
| R14.1 | stake-proportionality statistics | Discharged | S-QUORUM. |
| R14.2 | at the deployed committee size and τ | Open | *Needed: the R11.2 artefact (shared).* |
| R14.3 | manipulation bound | Open | *Needed: grinding/manipulation model (stake-splitting, key-registration timing) with a quantified advantage bound, extending S-QUORUM (sim · L).* |
| **R15** | **Equivocation contained** [P, C, T] | | |
| R15.1 | rules in the spec | Open | *Needed: equivocation premises in the Linear spec — no vote for an equivocated EB, two-announcement cap, disconnection (spec · M).* |
| R15.2 | negative conformance tests | Open | *Needed: re-enable the disabled negative tests against the new rules (spec · S).* |
| R15.3 | implementation contains equivocation | Failing ⚠ | Counter-evidence: X-AUDIT LEI-011, equivocation does not prevent voting — `TwoAnnouncements` is recorded and then discarded before the voting loop consults it; no fix filed as of 2026-10-06. *Needed: the node fix per LEI-011's recommendation (node · M); node-level test via X-ADV's fake-EB behaviours (spec · M).* |
| **R16** | **Nodes acquire and serve every promptly-announced EB** [C, T] | | |
| R16.1 | serving/retention obligation in the spec | Open | *Needed: the obligation as spec premises or verifier side-conditions — FFD currently abstracts diffusion away (spec · M).* |
| R16.2 | verifier checks serving | Open | *Needed: C-CHAIN consuming the `EBSent` events C-SCHEMA already defines (spec · M).* |
| R16.3 | two-node serving test | Open | *Needed: integration test requesting EBs the SUT did not vote for and does not prefer (infra · M).* |
| **R17** | **Praos history rules apply to EB transactions** [T] | | |
| R17.1 | EB storage feasibility | Discharged | B-SQLITE. |
| R17.2 | sync-from-genesis over certified EBs | Open | *Needed: E2E sync-from-genesis suite (infra · L).* Groundwork: B-SYNTH fixtures; every prototype state wipe (w38, w40 — D-CHANGELOG) has been a de facto genesis resync over certified EBs on Musashi, recorded nowhere as a test. |
| **R18** | **Node-to-client interfaces: certified txs inlined, minimal client change** [T] | | |
| R18.1 | client-interface changes tested and documented | Open | *Needed: E2E client-interface checks — db-sync, Mithril, wallet-visible behaviour (infra · L).* Survey only: D-IMPACT. |
| **R19** | **Mixed-version network safe and live through the hard fork** [T] | | |
| R19.1 | transition tested | Open | *Needed: automated mixed-version upgrade suite (infra · L).* Planned in D-IMPACT. |
| **R20** | **Heterogeneous conforming implementations interoperate** [C, T] | | |
| R20.1 | implementation-neutral conformance instrument | Discharged | C-VERIF, D-NETSPEC. |
| R20.2 | interoperation demonstrated | Open | *Needed: a second implementation to test against; the R21.2 gate keeps the instrument neutral meanwhile.* The Dingo (Go) node was removed from B-ANTI (ouroboros-leios #1104). X-ADV's Rust `net-node` speaks the Leios wire protocols to the prototype on devnets — a second implementation for attack, not a conforming one. |
| **R21** | **Implementations emit conforming execution traces** [T] | | |
| R21.1 | trace schema fixed and CI-validated | Discharged | C-SCHEMA. |
| R21.2 | node-emitted traces gated in CI | Open | C-CHAIN is in the maintained `hs-src` tree with its own Hspec suites and nix package (merged 2026-08-28), and the periodic re-verify of #1063 holds at tip on a live producer (X-FIELD). *Needed: a CI gate streaming testnet-harness node logs through it (infra · M).* Why it matters: the field verifier crash-looped unnoticed for about thirteen days on a PParams decode drift before its 2026-09-23 rebuild (X-FIELD). |
| **R22** | **BLS keys generated and the certificate built offline** [T] | | |
| R22.1 | key pair and proof of possession generated offline | Discharged | cardano-cli BLS key generation (#1355, master, with tests); the proof of possession is built into the registration certificate from the signing key (#1449), so no step needs a node or the network. |
| R22.2 | registering certificate built in the same session | Open | Groundwork: `stake-pool registration-certificate --bls-signing-key-file` (cardano-cli #1423), merged to the 11.2 integration branch, not yet master (#1439). *Needed: #1423 on master and a golden test of the certificate built offline (node · S).* |
| **R23** | **BLS keys registered in a dedicated certificate** [T] | | |
| R23.1 | dedicated certificate exists | Open | Nowhere yet: cardano-ledger #6048 was an exploration, closed; CIP draft cardano-scaling/CIPs#38. P-LLF's design note records a decision of 21 September — *no new registration certificate* for the first release — the day R23 was written to expect one at pv13. *Needed: a ruling reconciling R23 with the ledger formalisation's decision (docs · S), then the certificate itself (ledger · L).* |
| R23.2 | the initial-release vehicle cannot change parameters silently | Open | *Needed: a test that re-registering to rotate a key cannot alter margin, cost, pledge or relays by omission — the CLI restates them from chain state or refuses (node · S).* |
| **R24** | **Activation epoch known at submission, one active key per epoch** [C, T] | | |
| R24.1 | activation delay settled and applied deterministically | Discharged | cardano-ledger #6052 (the committee is seated when the mark snapshot rotates to set, so a key accepted in one epoch is active two boundaries later) and #6047 (time to live derived from the KES setup, ⌈maxKESEvo·slotsPerKESPeriod/epochLength⌉+2 epochs), both with ported tests; stated formally in P-LLF (`maxKeyAge`, committee materialised at `NEWEPOCH`, #1300). Note: requirements.md's Notation lists the activation delay and time to live as parameters; both are derived constants. |
| R24.2 | one active BLS key per pool per epoch | Discharged | By construction: one `individualPoolStakeBls` per pool in the pool distribution (cardano-ledger #5992) and one key per `LeiosSeat` in P-LLF (#1300). |
| **R25** | **Node starts with both keys and changes over without a restart** [T] | | |
| R25.1 | node accepts both keys at startup | Discharged | cardano-node #6697 with consensus #2303 (prototype-2026w38): `--shelley-bls-key` takes a JSON array of key envelopes and the node votes for every seat any of them holds; exercised by B-DEVNET's `VOTERS=N` key bundles. |
| R25.2 | no duty missed across the boundary | Open | *Needed: a devnet rotation test — active key plus registered successor loaded, votes and blocks counted across the epoch boundary (infra · M).* Groundwork: #2303 states the intent. |
| **R26** | **Votes signed with the active BLS key, matched from chain state** [C, T] | | |
| R26.1 | selection rule follows chain state | Open | Groundwork: consensus #2303 matches the loaded keys against the committee seats of the ledger's set snapshot, so only the epoch's registered key votes. *Needed: a test loading an active and a pending key and asserting the vote carries the active one (node · S).* |
| R26.2 | conformance evidence | Open | *Needed: C-CHAIN checking each vote's signature against the epoch committee's keys (spec · M); `blst` is already linked.* |
| **R27** | **Key states and expiration epoch queryable** [T] | | |
| R27.1 | active key, next key and expiration epoch reported | Open | Groundwork: the registered BLS key is visible in `StakePoolParameters` (cardano-api #1307). *Needed: a local-state query reporting active key, next key, activation and expiry epochs (node · M).* |
| R27.2 | time-to-live margin stated for the deployed parameterisation | Open | Groundwork: #6047 fixes the time to live at the KES lifetime rounded up to whole epochs plus two — about 21 epochs on mainnet, against the KES rotation cadence operators already follow. *Needed: that margin stated in operator documentation for the deployed parameterisation (docs · S).* |
| **R28** | **Every non-voting condition named to the operator** [T] | | |
| R28.1 | invalid proof of possession surfaced | Discharged | cardano-ledger #6085: Dijkstra's `POOL` rule rejects a registration whose proof of possession does not match, with the named predicate failure `BLSKeyInvalidProofOfPossession` (ImpTest). |
| R28.2 | pending, expired and missing keys surfaced | Open | Groundwork: #6047 leaves a seat keyless once its key expires. *Needed: node traces naming the pending, expired and missing-key conditions when a seat is held and no vote is cast (node · S).* |

Across the 28 requirements: 70 sub-items — **24 discharged, 41 open, 5 failing**. At requirement level (worst sub-item): 1 discharged (R24), 22 open, 5 failing (R5, R7, R12, R13, R15). The failing rows are the assurance machinery doing its job: each names its counter-evidence and its fix.

The needed artefacts, tallied from Table 1:

**Table 2 — Needed artefacts by owner and size.**

| Owner | S | M | L | Total |
|-------|---|---|---|-------|
| spec | 6 | 11 | 4 | 21 |
| sim | 3 | 7 | 1 | 11 |
| node | 4 | 7 | 0 | 11 |
| ledger | 0 | 0 | 1 | 1 |
| infra | 3 | 6 | 4 | 13 |
| docs | 2 | 0 | 0 | 2 |
| **All** | **18** | **31** | **10** | **59** |

Sequencing: within R3.2, the first item is independent and cheap, and `ChainLemma`/`SlotLemma` are in flight (spec PR #75) alongside R3.4 (PR #72); the R6.2, R10.2 and R13.2 measurements ride one testnet campaign on B-DEVNET; the slot-in-the-vote change fixes R5.3 and R12.3's node side together and is LEI-012's recommendation; R7.2 and R13.3 are node-team findings already filed; R23.1 needs a ruling before any artefact.

## Notes on the failing rows

- **R7.2 — certificate famine.** Vote floods through a single FIFO notification queue delay EB announcements, producing late-validation abstentions and skipped EBs at scale on the prototype devnet; found and measured by the live chain verifier (X-FIELD). The rule itself is sound in the spec; the fix is implementation-side.
- **R10.3 — unbounded retention.** X-AUDIT LEI-008: the SQLite LeiosDB grows without bound, so the disk-growth clause of R10 cannot currently be bounded at all.
- **R12.3 — deadline divergences.** The spec's point-in-time vote deadline versus the node's vote-when-validated behaviour, plus a sub-slot boundary mismatch (wall-clock node gates vs slot-granular spec); hundreds of datapoints per day from the field run, independently corroborated by X-AUDIT LEI-012. Whichever side moves, this is the process working: a ruling is owed, not just a fix.
- **R13.3 — delivery inefficiencies.** Announcements queue behind vote floods, and each vote is delivered roughly once per peer (~24×), eroding the diffusion budget the R13.1 model assumes available.
- **R15.3 — equivocation unchecked.** X-AUDIT LEI-011: observed announcement equivocation does not prevent voting. A spec-side gap first (the rule must exist before conformance can bind it) with the audit finding as standing counter-evidence.


## Artefact index

### P — formal proofs (repo: `ouroboros-leios-formal-spec`, dir `formal-spec/`, unless stated)

The spec typechecks under `--safe` with no postulates or holes: what is proved is machine-checked. Module-level hypotheses are the caveat, not proof gaps.

**Table 3.**

| ID | Location | What it is |
|----|----------|------------|
| P-SPEC | `Leios/Linear.lagda.md` (+ `Leios/Protocol`, `Blocks`, `Voting`, `FFD`, `Base`, …) | The normative small-step relation for Linear Leios: slot, fetch, base-ledger and role rules; encodes voting rules and the certification deadline. Current (post-pivot). |
| P-SAFETY | `Blockchain/Safety.agda`, `Blockchain/Safety/Transfer.agda` | States Common Prefix; proves the generic safety-*transfer* theorem: a Leios-style extension inherits CP from its base chain. Since PR #71 (2026-09-28) the protocol correspondence is a machine isomorphism (a bisimulation), not propositional equality. |
| P-LIVE | `Blockchain/Liveness.agda`, `Blockchain/Liveness/Transfer.agda` | States Honest Chain Growth and Existential Chain Quality; proves both transfer in each direction. |
| P-INST | `Network/Leios.agda` | Instantiates the transfer theorems for Linear Leios: `leiosSafety`, `leiosHCG`, `leios∃CQ`; proves RB-determines-EB injectivity. Parameterised on six unproved hypotheses (see caveats). |
| P-PROG | `Leios/Linear/Progress.agda` (PR #74, merged 2026-09-15) | Progress proof for the bare Linear Leios node: from any state with completed slot upkeep, the node runs through a whole slot (`tick`), iterates (`ticks`), and reaches every future slot (`enough-traces`), for arbitrary delivered messages and ranking blocks. Establishes non-vacuity of the invariant-style safety/liveness statements; the composite-node (with network shim and base layer) lemma is stated as future work (in flight: PR #72). |
| P-VOTE | `Leios/Voting/{Ideal,Real,Voter,Certifier}.lagda.md`, wired into `Network/Leios.agda` (PR #61, merged 2026-10-01) | Certificate correctness. `Ideal` proves that a certificate — `threshold` distinct voters — contains an honest voter whenever fewer than `threshold` parties are corrupt, and so that an honest party validated the block (`cert-correct`); `Real` abstracts concrete votes into the ideal state and transfers the theorem (`real-cert-correct`), conditional on honest valid votes being backed by validation; `Voter` is a per-node machine refining `Real`; `Certifier` is the shared functionality the Linear rules query. The Linear rules gained `Base₂` and `Cert₁`–`Cert₃` (stale certificate answers handled) and the windowed vote deadline `VT-Defer`. |
| P-LLF | repo `IntersectMBO/formal-ledger-specifications`, `Ledger.Dijkstra.Specification.Leios{,.Validity}` (branch `leios-main`, parts on `master`); design note `docs/leios/design-note.md`; tracking issue #1295 | The Leios Ledger Formalisation: Leios protocol parameters (#1317), the crypto structure and primitive types (#1304), BLS keys on stake pools (#1331), the voting committee with `maxKeyAge` and `honouredBlsKey` materialised at `NEWEPOCH` (#1300), `ValidEB` with its valid-extension conjunct through `LEDGERS` (#1330, master), `certificationDelay` (#1340, master). In flight: `ValidEBCert` (#1333), block structure and the `CHAIN` rule (#1339, #1346), committee rotation (#1342). Makes ledger law of what the prototype enforces by convention; its design decisions bind R2 and R22–R28. |

### C — conformance

**Table 4.**

| ID | Location | What it is |
|----|----------|------------|
| C-VERIF | formal spec: `Leios/Linear/Trace/Verifier.lagda.md` (+ `Verifier/Test.lagda.md`) | Certified trace verifier: `verifyTrace` returns a correctness proof or a typed failure proof for any candidate execution trace. Since PR #61 it decides the certificate steps from their generated premises, and the test module exercises the certificate firing, a tip change under an outstanding query, and rejected certificate steps. |
| C-EXTRACT | `leios-trace-verifier/` | MAlonzo-extracted Haskell verifier over simulator JSONL; golden corpus in `conformance-traces/` (5 valid, 2 invalid), Hspec runner, gated by `.github/workflows/conformance.yaml`. Property-based suite exists but is disabled (pre-pivot generators). |
| C-CHAIN | `leios-trace-verifier/hs-src/app/linear-chain/`, `hs-src/src/LinearLeiosChain.hs`, `src/LinearLeiosVerifierChain.agda`, `leios-trace-hs/src/ChainEvents.hs`; tests `hs-src/test/Spec/Chain{Events,Segments,Verifier}.hs`; packaged in `nix/trace-verifier.nix` (merged to main 2026-08-28) | Live-node streaming verifier (`linear-leios-trace-verifier-chain`): reads node logs, queries leadership schedule and stake from a running node via `cardano-api`, re-verifies periodically rather than per slot (#1063). The highest-value implementation-conformance instrument; now in the maintained tree with its own test suites, but not yet run by CI against node-emitted traces. |
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
| S-POSTCIP | `post-cip/` (catalogue in `post-cip/README.md`), `analysis/markov/` | Post-CIP findings for Linear Leios: a Markov model of EB certification (Lean), the `apply-reapply` regression of mainnet `db-analyser` data (CPU of `Apply` versus `Reapply` by block size, transaction count, inputs and Plutus steps), the resource-constraint model (three cores suffice for a typical 12 MB EB; adversarial late release of bodies can double peak CPU), idealised mempool diffusion and fragmentation, front-running exposure, bandwidth–latency, UTxO set size and lifetime, block utilisation. |

### B — benchmarks and prototype measurement

**Table 6.**

| ID | Location | What it is |
|----|----------|------------|
| B-CRYPTO | `crypto-benchmarks.rs/` | Reference BLS voting/certificate implementation with Criterion benchmarks (vote, VRF, sortition, Fait-Accompli, serialisation) and correctness tests; CI-gated. Feeds the simulators' CPU model. |
| B-COST | `docs/cost-estimate/` | Per-resource operating-cost analysis (CPU, RAM, storage, egress, IOPS) with aggregate cost table, fee formula and TPS break-even. |
| B-SQLITE | `docs/targeted-design-investigations/microbenchmark-sqlite/` | Measured feasibility of EB storage on a relational store: closure/body query latency, index overhead, pruning, churn. |
| B-ANTI | `antithesis/` | Deterministic-simulation testing of the real `cardano-node-leios`: devnet under adversarial scheduling and fault injection, WAN emulation; computes cross-node liveness, TPS and latency metrics; CI-submitted. The Dingo (Go) node setup was removed (#1104, 2026-09-19). |
| B-DEVNET | `demo/proto-devnet/`, `demo/dozen-devnet/` (+ x-ray Grafana dashboards: voting, diffusion, LeiosDB; Alloy facets) | Reproducible devnets of the real prototype: a three-node proto-devnet and a twelve-node dozen-devnet with realistic peer degree built for throughput experiments; `VOTERS=N` adds committee members whose BLS keys the producers vote with as bundles. The dashboards are the measurement instruments for diffusion (#1096, #1102 open), voting participation and LeiosDB partition sizes (#1054). |
| B-BURST | `demo/burst/` | Protocol-burst demo: a mocked upstream peer releases ten 12.5 MB EBs just before a Praos block's slot onset (a small ATK-LeiosProtocolBurst) under Linux traffic-control WAN emulation, measuring the effect on RB diffusion; the bufferbloat lesson is recorded. The hardware instrument for R1/R5. |
| B-SYNTH | `ouroboros-consensus` `db-synthesizer` (#2241, #2283; replay from a file #2339 open) with `ouroboros-consensus-tools/check-synth-fixture`; `cardano-node` #6700 (replayable Dijkstra transaction stream) | Forges Leios chains offline: blocks filled with a respending transaction stream, overflow into announced EBs, votes signed from the ledger's committee, certificates in later blocks. Fixture generator for sync, replay and DB tools; no vote window or announcement deadline modelled. |

### T — test suites

Implementation test suites largely ride inside the artefacts above (C-EXTRACT's golden tests, B-CRYPTO's correctness tests, B-ANTI's metric-parser tests, the Haskell simulator's config/topology suite). No standalone T artefact in this repo discharges a requirement on its own; R17–R19 await the E2E and upgrade suites planned in D-IMPACT. R22–R28 draw on the implementation repos' own suites — cardano-ledger ImpTests (#6085, #6052, #6047), cardano-cli tests (#1355) — and on B-DEVNET's key-bundle runs; the rows cite the PRs.

### D — design and methodology documents (context, not evidence)

**Table 7.**

| ID | Location | What it is |
|----|----------|------------|
| D-IMPACT | `docs/ImpactAnalysis.md` | Per-area impact analysis; its "prototypes and experiments for derisking" and end-to-end-testing sections are the planned-artefact list for R17–R19. |
| D-DESIGN | `docs/leios-design/` | Design report; "Assumptions to validate early" and the risk analyses (data withholding, protocol bursts) are direct sources of future matrix rows. |
| D-FETCH | `docs/targeted-design-investigations/a-baseline-LeiosFetch-design/` | Baseline LeiosFetch and relational-storage design. |
| D-NETSPEC | `simulation/docs/network-spec/` | Mini-protocol network specification. |
| D-THREAT | `docs/threat-model.md`, `docs/mev/` | Threat model (current, post-pivot; MEV threats regrouped 2026-09-29) and MEV research set for Linear Leios. Its T-numbers key X-ADV's behaviours (T11, T15, T22, T23). |
| D-CHANGELOG | `CHANGELOG.md` | Prototype release notes (prototype-2026w36 … w40): what shipped in which release, with the consensus/node/ledger PRs and audit findings each closes. The provenance for every row that cites a prototype version. |

### X — external and field evidence

**Table 8.**

| ID | Location | What it is |
|----|----------|------------|
| X-AUDIT | `audits/anastasia-labs-leios-audit-2026-09-01.pdf` | Third-party security audit (Anastasia Labs, v1.0, 2026-09-01) of the Leios consensus implementation: findings LEI-001–LEI-014, each with recommendation and resolution; publicly shareable per its disclosure statement. Since then: LEI-004/005/009 closed by consensus #2358 (w40); LEI-008 addressed by #2261 (w38); LEI-011 and LEI-012 unresolved. |
| X-CRYPTOREV | `docs/arc-voting-crypto-review.pdf` | External cryptographic review of the voting scheme. |
| X-PAPER | `docs/leiospaper-submitted.pdf` | The submitted Leios research paper (protocol security analysis). |
| X-FIELD | out-of-repo (Taylor): `verifier-findings-report.md`; in the repo root, uncommitted: `FINDINGS.md` (organised findings, 2026-08-23), `announcement-path-finding.md` (2026-08-20), `governor-wedge-report.md` with the ITree-CSP model `governor-wedge-model/Wedge.agda` (2026-09-29), `NITEN-OPS.md` (verifier operations log), `data/bench-niten-noadx-20260922.txt` | Field evidence from continuous live-node trace verification of a real Musashi block producer (since 2026-08-05): the voting-deadline divergence and receipt-freshness violations (R12), certificate famine and its announcement-path cause (R7), tracer and PParams drift (R21); the relay inbound-governor wedge on w38–w39 with its fix identified upstream and machine-checked in CSP (R1); B-CRYPTO's benchmarks run on SPO-grade hardware without ADX (R10). Should be committed or superseded by repo artefacts. |
| X-LEDGER | out-of-repo: `ledger-leios-inventory.md` (Taylor) | What the prototype's ledger integration actually implements, from pinned sources — descriptive input to R2. |
| X-ADV | repo `input-output-hk/leios-tools` (`shared-rs` behaviour tree: eb-burst #91, fetch-flood #96, malformed-eb #97, single-bls-cert #100); actuation, behaviour trees and results in the *private* `leios-adversarial-tools` repo (`threats/tNN/report.md`) | Wire-level adversarial node (`net-node`, Rust) with pluggable behaviours keyed to D-THREAT's T-numbers, run against the real prototype on fresh devnets. Results so far: T15 forged certificates all rejected; T23 bursts of twenty and a hundred real EBs with no measurable harm and no stale EB certified. Provenance is weaker than a `sim-cli.hash`: only the engine half is public. |

## Cross-cutting caveats

1. **The formal safety/liveness results are conditional transfer theorems.** P-SAFETY/P-LIVE prove that Leios *inherits* Common Prefix, Honest Chain Growth and Existential Chain Quality from Praos; P-INST applies them, but is module-parameterised on five unproved hypotheses (hash correctness and uniqueness, purity, the base chain being a blockchain, and the per-deployment Chain and Slot lemmas); extension equality went with `ChannelCat` in PR #71, and the Chain and Slot lemma proofs are in flight in PR #75. Rows citing P-SAFETY/P-LIVE/P-INST are conditional until these are discharged. P-PROG removes the vacuity concern for the bare node (the trace sets the theorems quantify over are non-trivial); the composite-node progress lemma remains future work (R3.4). There is no absolute Leios safety proof, and no formal model of cryptographic hardness (BLS, VRF) anywhere in the P route.
2. **Property-based conformance is dark.** Only seven golden traces gate CI; the QuickCheck trace-generation suite is disabled pending its port from Short to Linear Leios (still commented out in `hs-src/test/Spec.hs` on 2026-10-06). Until it returns, C evidence is thin for anything the golden traces and the spec's own test module do not touch.
3. **Live conformance is proven possible but not yet institutionalised.** C-CHAIN runs continuously against a real block producer (X-FIELD) and is now in the maintained tree with tests, but no CI exercises node-emitted traces — the R21 drift does recur unnoticed: the field verifier crash-looped for about thirteen days on a PParams decode drift before anyone saw it (X-FIELD, rebuilt 2026-09-23).
4. **Simulator provenance is out-of-repo.** The current Rust simulator was extracted to `leios-tools`, which has since also grown a wire-level adversarial net-node with pluggable behaviours (eb-burst/T23, vote-flood, fake-EB variants) — the natural instrument for the R1/R5 campaigns and the R7.2/R13.3 fixes — but its actuation and results live in a private repository (X-ADV), so only the engine half can be cited; S citations rest on each campaign's `sim-cli.hash`. The in-repo Haskell simulator is substantially pre-pivot (Short Leios core with a Linear variant layered on IB-shaped machinery) — usable for trace generation, weak as behavioural evidence.
5. **Composition rule.** Per the requirements' Notation: C artefacts carry weight only in composition with the P and S artefacts establishing that the specification itself satisfies the requirement. Several clauses discharged on the C route are P-conditional; they inherit caveat 1.
6. **The ledger half is being formalised elsewhere, and has already ruled on one requirement.** P-LLF makes ledger law of what the prototype enforces by convention — committee, key age, EB validity, certification delay — on `leios-main` and `master` of `formal-ledger-specifications`, outside this repo. Its design note's decision of 21 September, no new registration certificate for the first release, conflicts with R23 as written the same day; the two documents need one ruling (R23.1). Rows R24.1, R24.2 and R28.1 are discharged by ledger implementation and tests whose formal counterpart is P-LLF, so they are as current as that branch.

## Excluded artefacts

Pre-pivot (Short/Full Leios, input-block era) material is not cited as evidence: `docs/protocol-testing.md` and `docs/simulation-model-parameters.md` (IB-era test plans), `docs/technical-report-1.md` and `docs/Short-Pipeline Leios.md` (historical), the 2025 weekly campaigns under `analysis/sims/`, the Haskell simulator's scenario sets, `docs/obsolete-report/`, and the disabled property-based conformance generators. Where one of these is the only material near a clause, the clause is marked Open with no bearing artefacts.

## Revision notes

- **2026-10-06.** Survey of all repos since 2026-09-15. New artefacts: P-VOTE, P-LLF, S-POSTCIP, B-DEVNET, B-BURST, B-SYNTH, X-ADV, D-CHANGELOG; C-CHAIN relocated to the maintained tree; P-PROG merged. Rows changed: R7.3 and R22.1, R24.1, R24.2, R25.1, R28.1 to Discharged; R10.3 from Failing to Open (LEI-008 resolved by garbage collection, measurement outstanding); R5.3 from Open to Failing (unbounded vote state, consensus #2367); R12.3's spec side settled, node side still failing; R3.2 reduced to five hypotheses with two in flight; the R22–R28 artefact cells filled. Flagged for a ruling: R23 versus the ledger formalisation's no-new-certificate decision; the Notation's "parameters" for activation delay and time to live are derived constants.

## Maintenance

- When an artefact lands or changes, update its index entry and every requirement row citing it; every artefact must itself cite the requirement identifiers it discharges (requirements.md, Notation).
- A requirement is **Discharged** only when every sub-item is: each artefact current, stating its parameter ranges — including the hardware and percentile clauses where the requirement states them.
- ⚠ divergences are tracked defects: record the ruling (spec change, implementation change, or parameter change) and its artefact before clearing the flag.