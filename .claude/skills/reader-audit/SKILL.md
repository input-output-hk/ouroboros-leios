---
name: reader-audit
description: Read a document as a specified reader and report every place that reader would stall for lack of context, ranked by severity. Use before hand-off of an assessment or report, or when a reader says a document assumes too much. Also holds this repository's canonical document-class reader table.
---

# Skill: Reader Audit

Read a document **as a specified reader** and report every place that reader would stall for lack of context. This operationalizes theory-of-mind (Pinker's "curse of knowledge"): the author cannot un-know what they know, so they cannot feel where the reader lacks the scaffolding. The most common failure of this kind is **assumed cross-document context** — a document written for the author who has read everything, not for the reader who actually shows up. In this repository it has a characteristic second form: **assumed layer context**, where the author knows whether a claim is about the paper, the specification, the simulator, or a deployed network, and the reader cannot tell.

Self-contained instructions only; runs nothing. This is an audit: it flags and suggests, it does not rewrite. Pair it with `tighten-prose`, `executive-summary`, `abstract`, or `humanize-prose` to apply fixes.

## When to Use

- Before hand-off of an assessment, synthesis artifact, explainer, or report.
- As the reader-fit / context self-containment dimension of a quality check on a document.
- When a reader says a document "assumes too much" or "you had to have read everything else."

Not for: internal team-facing documents where high context assumption is by design (journal, experiment `design-history.md` / `lessons-learned.md`) unless explicitly asked; rewriting (this skill only diagnoses).

## Step 1: fix the reader

The audit is only meaningful against a named reader, because the **context budget is set by the reader, not the author**. Take the persona from the invocation if given; otherwise infer the document class from its path and use that class's reader from the table below. State which reader you are using before auditing.

### Document classes and their readers

This table is the canonical reader definition for this repository. The sibling prose skills (`humanize-prose`, `tighten-prose`) refer to it.

| Class | Path | Reader | Context budget |
|-------|------|--------|----------------|
| Assessment / deep dive | `assessments/` | A blockchain or distributed-systems engineer who does **not** work on Leios | Assumes general distributed-systems and consensus vocabulary (BFT, quorum, VRF, Merkle tree, longest-chain vs. BFT finality). Assumes **no** Leios terms of art and **no** prior document from this repository. |
| Synthesis artifact / brief / explainer | `artifacts/` | A general technical reader deciding something | Expands everything domain-specific, including the Leios block-class abbreviations. Decision-oriented. |
| Protocol cheatsheet | `artifacts/leios-cheatsheet.md` | A new team member on day one | Every entry self-contained and objective, with at least one source link. Zero assumed prior reading. |
| Weekly report | `weekly-reports/` | A technical stakeholder who is not a Leios specialist | One-line gloss for anything Leios-specific; numbers with comparators. Readable without the journal. |
| Formal-methods note | wherever filed | A formal-methods engineer | Assumes the notation (Agda, TLA+) and proof vocabulary; assumes **no** Leios mechanics. |
| Journal / experiment log | `journal/`, `experiments/*/design-history.md`, `experiments/*/lessons-learned.md` | The core team | High context assumption is by design. Do not audit unless explicitly asked. |

The key consequence: flag against the *persona's* assumed knowledge, not your own. For the assessment class's blockchain-engineer reader, do not flag "BFT" or "Merkle tree"; do flag Leios terms of art — the block-class abbreviations, stage and pipeline names, bare parameter symbols — and any result from another document in this repository that is cited as if the reader had read it. For the `artifacts/` general-technical reader, flag both.

## Step 2: read once, tracking what you do not yet know

Read the whole document start to finish in the persona, maintaining a running model of what that reader knows so far. A term defined on line 40 does not help a reader who needed it on line 10. Note each point where the running model is insufficient to follow the next sentence.

## Stall taxonomy (what to flag)

1. **Undefined term of art or acronym** — used before it is defined *in this document* (repository-wide prior definition does not count).
2. **Unglossed reference to other work** — "as the diffusion experiment showed," "per #287," a bare file link — without the one-line point the reader needs. The fix is a glossable reference: state the conclusion, then link.
3. **Number asserted as known** — a throughput ceiling or latency figure cited as if memorized, with no in-document source, definition, or parameterization.
4. **Layer ambiguity** — a claim that does not say whether it is about the paper, the formal specification, a simulator, an implementation, or a deployed network. For this repository's readers that is a stall, not a nuance.
5. **Dependency on an unstated conclusion** — the argument needs a result established elsewhere and never restates it, so a reader without that document silently loses the thread.
6. **Missing orientation / onramp** — no early statement of what the document is, for whom, and what it assumes.
7. **Curse-of-knowledge leap** — a reasoning step obvious to the author that skips something the reader needs to follow the logic.
8. **"We all know" framing** — project-internal references (a meeting, a person, an unnamed prior decision) a reader outside the team cannot resolve. In outward-facing documents these are also a convention violation.

## Step 3: record each stall

For each, capture:

- **Location** — a short quote or the line, so the author can find it.
- **Stall** — what the reader does not have at that point.
- **Type** — one of the taxonomy above.
- **Severity** — **Blocks** (reader cannot follow), **Slows** (reader can limp on but stumbles), or **Minor** (a polish issue).
- **Fix** — the minimal repair: define the term, add a one-line gloss plus link, restate the borrowed conclusion in a clause, or add an onramp. Keep fixes spare; full self-containment fights concision, so restate only the load-bearing point and link for depth.

Rank Blocks first.

## Respect the context budget

- Do not flag knowledge the persona is assumed to have. Over-flagging trains the author to ignore the audit.
- Do not push a document past its class's budget: assessments may stay dense for experts, internal notes may assume the team. The target is self-containment *for the stated reader*, not universal accessibility.
- Tiering and progressive disclosure resolve the tension with concision: a self-contained summary or abstract at the top (see the `abstract` skill) lets the body assume more.

## Invariants

- **Invent nothing.** A suggested restatement uses only facts already in the source. If a borrowed conclusion is needed but absent, flag that it must be fetched from its source document; do not reconstruct it from memory.
- American English.

## Output

A short header naming the reader and document class, then the ranked findings. A findings table works well:

| # | Location | Reader stall | Type | Severity | Suggested fix |
|---|----------|--------------|------|----------|---------------|

Close with, when warranted, a drafted 2-4 sentence **onramp** the author can drop at the top (built only from facts in the document), and a one-line overall read on whether the document meets its class's context budget.

## Related skills

`tighten-prose`, `executive-summary`, `abstract`, `highlights` (apply the fixes), `humanize-prose` (tone and de-AI pass). The document-class reader table above is the canonical reader definition for this repository; keep it in sync with the repository blueprint in [AGENTS.md](../../../AGENTS.md).
