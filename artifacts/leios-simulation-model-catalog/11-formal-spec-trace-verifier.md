# Deep Dive 11: Formal Specification and Trace Verifier

**Created:** 2026-09-16
**Status:** Draft for review.
**Provenance:** 🤖 (LLM-generated from source reading, pending human review)
**Read at:** [`input-output-hk/ouroboros-leios-formal-spec`](https://github.com/input-output-hk/ouroboros-leios-formal-spec) @ HEAD of 2026-09-15 (~4,000 lines of Agda across 30 modules); [`ouroboros-leios/leios-trace-verifier/`](https://github.com/input-output-hk/ouroboros-leios/tree/main/leios-trace-verifier) and `leios-trace-hs/` @ `11be715`.
**Parent entry:** [catalog § Formal specification and trace verifier](../leios-simulation-model-catalog.md#11-formal-specification-and-trace-verifier)

The machine-checked end of the catalog: a relational Agda specification of Linear Leios with safety and liveness proofs, and the certified conformance checker extracted from it — the instrument by which every simulator's and implementation's *protocol logic* is judged. **Actively developed** (Yves Hauser, latest proofs merged 2026-09-15).

---

## 1. The specification

- **Structure.** `Leios.Linear` (small-step relational semantics with slot "upkeep" obligations — a node must discharge Base/EB-Role/VT-Role checks each slot before advancing, which is how "an honest node never silently skips its duties" is encoded), over abstract interfaces: `Leios.Abstract` (crypto, hashing, `splitTxs`), `Leios.FFD` (freshest-first diffusion as an abstract functionality), `Leios.VRF`, `Leios.Voting`, `Leios.KeyRegistration`, `Leios.Base` (the Praos base chain). Built on the `categorical-crypto` composable-machines library (channels, machine composition), with modules compiled under Agda's `--safe` flag (no postulates in the safe modules).
- **Proofs.** `Blockchain.Safety`/`Blockchain.Liveness` state a generic spec/deployment framework — n nodes, honest ones running the spec machine, **the rest completely arbitrary** — with transfer theorems (`Safety/Transfer`, `Liveness/Transfer`) that carry common prefix, healthy chain growth, and existential chain quality from an assumed-safe base chain to the composed Leios network (`Network.Leios`, over a k-delayed diffusion functionality). Recent work (merged 2026-09-15) adds **progress**: a proof that the Linear Leios node completes every slot.
- **What "the adversary" is here:** arbitrary machines at non-honest indices plus an adversarial channel — categorically unconstrained, in contrast to every quantitative model's specific adversary (abstention in `linleios`, tarpits in the Mininet bed, behavior trees in sim-rs/Piranha). The proofs bound what *any* adversary can do to safety/liveness given base-chain assumptions; they say nothing quantitative about throughput under attack.

## 2. Mempool and transaction caches (standing section)

The spec's mempool is **`ToPropose : List Tx` — an abstract, unbounded list fed by the environment** (`SUBMIT (EB ⊎ List Tx)` inputs; a `FetchLdgI/O` channel exposes ledger reads). At production time the abstract `splitTxs : List Tx → List Tx × List Tx` divides it into RB-payload and EB-payload; the Linear document states an EB carries "the transactions currently stored in the mempool." EBs are retained in `EBs' : List (ℕ × EndorserBlock)` (tagged with reception slot) and votes in `Vs`; **no capacity, eviction, TTL, or fetch mechanics exist at this level** — TX diffusion and mempool management are environment behavior, below the spec's abstraction floor. Consequences for our study: (a) the trace verifier **cannot detect mempool-management misbehavior** (backlog handling, cache eviction, write-back policy are all unconstrained); (b) conversely, any mempool policy we propose is automatically conformant as long as the produced blocks and votes satisfy the relational rules — the spec constrains *what* is proposed and voted, not *how* the proposal set was maintained.

## 3. The trace verifier

Derived from the spec (`Leios.Linear.Trace.Verifier`, `--safe`): traces are reduced to `Action` sequences (EB-Role, VT-Role, …) and checked against the relational semantics by a **decidable** procedure — a certified checker, deliberately *not* a deterministic reference implementation, so differently-scheduled honest implementations all pass. The Haskell packaging (`leios-trace-verifier`, via extraction + `leios-trace-hs` shared schema) ships two executables:

- **`linear-leios-trace-verifier`** — file-based: topology + config + trace (from the Rust or Haskell simulator with `--conformance-events`, or a node log), batch or `--streaming` incremental; no cardano-api dependency.
- **`linear-leios-trace-verifier-chain`** — **live-node mode**: streams the trace from stdin and sources the system-under-test's leadership schedule and stake distribution *from a running node via cardano-api* (stage lengths fixed at L_vote = 4, L_diff = 7). This is the mode behind the Aug-2026 milestone — Ramsay Taylor running it as a live network monitor on his own testnet node, and processing other operators' logs ([Confluence blog](https://input-output.atlassian.net/wiki/spaces/NC/blog/2026/08/20/6219563009/Leios+Team+develops+safe+and+live+trace+verifier+for+protocol+conformance+testing)).

A `conformance-coverage.md` and stored `conformance-traces/` document what the checker exercises. Lineage: the "computational meaning" trace-verifier idea originated in the ARC Jolteon/FastBFT project (Mauro Jaskelioff), was built for Leios by Andre Knispel and Yves Hauser, and extended to live nodes by Ramsay Taylor, Yves Hauser, and Javier Díaz.

## 4. Assessment against the four catalog dimensions

- **Faithfulness.** This artifact *defines* protocol faithfulness for everything else in the catalog; its own fidelity risk is spec-vs-CIP divergence (the CIP is prose; the Agda is the machine-checked shadow — which of the two is normative when they disagree is a governance question, not a technical one ❓).
- **Status.** Actively developed: progress/liveness proofs landing Sept 2026; the verifier operational against simulators and live testnet nodes.
- **Scope.** Linear Leios node behavior, safety (CP/HCG/∃CQ via base-chain transfer), liveness/progress; conformance checking of traces. Not: performance, timing distributions, mempool policy, or network mechanics (FFD is abstract).
- **Performance.** The checker is fast enough to run as a **live monitor** on a real node — a notable property for a proof-assistant-extracted artifact.

## 5. Follow-up questions

1. **Spec-vs-CIP divergence tracking**: is there a maintained correspondence (CIP section ↔ Agda rule)? Nothing found in this pass ❓ — for our troubleshooting charter, knowing which document wins matters.
2. The mempool abstraction floor (§ 2) means our alignment study needs its *own* conformance notion (e.g., smol world's blocking admission vs. real backpressure can't be adjudicated by the verifier); worth stating explicitly in the study design.
3. Whether the verifier could be *extended* downward — e.g., checking EB-content properties like "every referenced tx was previously announced" — to give mempool-adjacent conformance; ask Hauser/Knispel how hard the schema change would be.
4. `Leios/Linear/Progress.agda` and the 2026-09 progress proofs deserve a read when we study liveness under load — they encode exactly which upkeep obligations "completing a slot" comprises.

## Sources

- Read at `ouroboros-leios-formal-spec` HEAD (2026-09-15): `formal-spec/Leios/{Linear.lagda.md, Protocol.lagda.md, Abstract.lagda.md, Linear/Trace/Verifier.lagda.md}`, `Blockchain/{Safety,Liveness}.agda` heads, `Network/Leios.agda`, module inventory; repo README
- Read at `ouroboros-leios@11be715`: `leios-trace-verifier/ReadMe.md`, directory inventory (`conformance-coverage.md`, `conformance-traces/`); `leios-trace-hs/` module list
- [Trace verifier on live nodes — #formal-methods, 2026-08-20](https://input-output-rnd.slack.com/archives/C4WQQKUU9/p1787228866642259) (James Chapman; internal); [Confluence blog, 2026-08-20](https://input-output.atlassian.net/wiki/spaces/NC/blog/2026/08/20/6219563009/Leios+Team+develops+safe+and+live+trace+verifier+for+protocol+conformance+testing) (internal)
- [Catalog entry 11](../leios-simulation-model-catalog.md#11-formal-specification-and-trace-verifier)
