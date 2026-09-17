# Ouroboros Leios — Exploration and Troubleshooting

Research-and-development exploration of [Ouroboros Leios](https://github.com/input-output-hk/ouroboros-leios), the Cardano throughput-scaling protocol ([CIP-0164](https://github.com/cardano-foundation/CIPs/blob/d07a30bca36a28535afa151915bb4900b2116d3a/CIP-0164/README.md)). This repository is a working notebook, not a deliverable: it holds the survey work, source-level maps, diagrams, verified facts, and process lessons that a scope decision will rest on.

**Provenance:** ⏳🤖 LLM-generated index, pending human review · **Charter and conventions:** [AGENTS.md](./AGENTS.md)

> [!NOTE]
>
> **Phase 0 — scope discovery.** The deliverable of this phase is a written scope statement with candidate workstreams, sized and ranked. It is deliberately **not yet written**: it waits on the scope brainstorm of **2026-09-21**. Several candidates have emerged from the work below, including an implementation-conformance workstream; they have not yet been consolidated or ranked.

## Start here, by question

| If you want to know… | Read |
|---|---|
| What simulators and models of Leios exist, and how faithful, current, and capable is each? | [Catalog of Leios simulations and models](./artifacts/leios-simulation-model-catalog.md) — 12 entries, plus a [per-entry dossier](./artifacts/leios-simulation-model-catalog/) with commit pins |
| Where is the production Leios code staged, and on which branches? | [Leios production staging branches](./artifacts/cardano-node-status.md) |
| How does a transaction actually move through the prototype node? | [Transaction-lifecycle diagram](./artifacts/leios-node-tx-lifecycle.svg), backed by [the mempool and LeiosTxCache map](./artifacts/leios-node-mempool-txcache.md) |
| Which parameters and inequalities decide whether blocks, votes, and certificates are created and accepted — and which are actually enforced? | [Protocol parameters and admission inequalities](./artifacts/leios-node-protocol-parameters.md), with the [timing-inequalities timeline](./artifacts/leios-timing-inequalities.svg) |
| How do the kleioscan chain metrics, the node's telemetry funnel, and the models' alignment quantities line up? | [Mempool-alignment metric mapping](./artifacts/leios-mempool-metrics-mapping.md) |
| What does a Leios term or parameter mean? | [Leios cheatsheet](./artifacts/leios-cheatsheet.md) — written for a new team member on day one |
| What have we actually confirmed, with a date and a source? | [facts.md](./facts.md) |
| What was done, when, and why? | [journal/phase-0.md](./journal/phase-0.md) (reverse-chronological) |
| What have we learned about *how* to do this work? | [meta-lessons-learned.md](./meta-lessons-learned.md) |

## Layout

- `AGENTS.md` — the charter: mission, goals, constraints, repository blueprint, conventions, and analysis instructions. Read before contributing.
- `CLAUDE.md` — Claude-specific addenda; defers to `AGENTS.md`.
- `artifacts/` — synthesis documents, source maps, and diagrams (the table above).
- `journal/` — dated work log, newest first. A historical record: existing text is not edited.
- `facts.md` — verified findings, each with its date, source, and layer.
- `meta-lessons-learned.md` — append-only log of methodology and process lessons.
- `.claude/skills/` — agent skills ported from a sibling consensus study and retargeted here.
- `flake.nix` / `flake.lock` — the Nix development shell, **inherited from that sibling study and not yet pruned** for Leios.

Directories named in the blueprint but not yet created — `experiments/`, `assessments/`, `weekly-reports/` — are absent because nothing in Phase 0 has needed them yet.

## How to read the records

**Everything about the implementation is pinned.** The Leios code moves daily, so source claims cite an exact commit and the documents say so at the top. The current pin set is `ouroboros-consensus @ b56977b`, `cardano-node @ 7e33674`, `cardano-ledger @ 1587f21`, `cardano-base @ fbfb3f0` (2026-09-16), with deployed values read from the musashi testnet configuration on 2026-09-17. **Permalinks stay valid; branch tips diverge within days** — re-pin before relying on any of it, using the re-verification commands embedded in each document.

**Claims carry their layer.** A statement about the paper, the formal specification, a simulator, the implementation, and a deployed network are five different things, and the documents distinguish them. Where a number is an estimate rather than a measurement it is marked ❓ **SCRUTINY**, or ❓🤖 when it came from LLM-assisted reasoning.

**Provenance is explicit.** 🤖 means LLM-generated and human-reviewed; 👱🤖 human-drafted and LLM-refined; 🤖👱 the reverse; unmarked means human-written. See `AGENTS.md` § Conventions for the full marker set.

**Corrections are additive.** Journal entries are frozen once written; a later finding is recorded as a dated `> [!WARNING]` callout at the point of the error, leaving the original wording in place. Several such corrections already exist — they are the record working as intended, not noise.

## Temporary hosting and deliberate absences

The standalone history is temporarily published as the unrelated [`bwbush/tmp-explorations`](https://github.com/input-output-hk/ouroboros-leios/tree/bwbush/tmp-explorations) branch of `ouroboros-leios`; it is not a normal feature branch or pull-request precursor. There is no ticket board. The repository structure itself stays provisional until after the scope decision.
