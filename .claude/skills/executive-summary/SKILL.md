---
name: executive-summary
description: Write a concise summary for a general technical audience who is reading to decide something - the weekly-report and executive-summary register. Use for weekly reports, stakeholder briefs, or any summary whose reader is technical but not a specialist.
---

# Skill: Executive Summary

Write a concise summary for a **general technical audience**: a competent reader who is not a specialist in this sub-topic and is reading to decide something. This is the weekly-report / executive-summary register. It is one of four sibling summary skills; this one is defined by its audience, and it may translate specialist detail down and drop it.

Self-contained instructions only; runs nothing.

## When to Use

- Weekly reports, executive summaries, stakeholder briefs.
- Any summary whose reader is technical but not a specialist, and who acts on it.

Not for: specialist-to-specialist condensation (use `tighten-prose`), self-contained research abstracts (use `abstract`), promotional pointer lists (use `highlights`).

## Audience and register

General-technical. Expand every acronym on first use; give a one-line plain gloss for the one term a non-specialist would stall on. Neutral and decision-oriented. No enthusiasm adjectives.

## What to keep, what to cut

- **Keep:** the result, its number, and the decision implication.
- **Cut:** procedure, specialist derivation detail, and any sentence that would not change what the reader does.

## Structure

Per topic, use the Completed / Findings / Why-it-matters skeleton:

- **Completed.** What happened, factual past tense, one or two sentences.
- **Findings.** Bullets; each one result, led by its point, carrying its number.
- **Why it matters.** One or two sentences translating the finding into a decision or next action.

Budget roughly 400-700 words. A narrative variant (one paragraph plus a "Why it matters" line per topic) is acceptable.

## Core moves

- Bottom line up front: lead with the conclusion and its number, not the background.
- One idea per sentence; every sentence earns its place.
- Quantify: number with unit and a comparator or range ("a 10x range, 15-198 tx/s").
- Method in a clause, not a section.
- Contrast sharpens: "latency-bound, not cost-bound."

## Two tests

- **So-what:** for each sentence, what does the reader do differently? If nothing, cut or merge.
- **Stand-alone:** could a reader act correctly on the summary without opening the document?

## Exemplars

No local exemplars yet — this repository is new. Link the first weekly report that lands the Completed / Findings / Why-it-matters skeleton cleanly, and the first that carries the narrative-paragraph variant, once each exists under `weekly-reports/`.

## Invariants

Numbers, names, dates, and citations exact; keep any caveat that changes the conclusion; American English; self-contained (no ticket-number cross-references).

## Technical tone

Follow the middle-ground technical register in `humanize-prose` § Technical tone: plain verbs over nominalizations, active voice by default, calibrated confidence over hedge stacks, no evaluative adjectives, concrete over abstract, declarative and direct, restrained first-person-plural, minimal metadiscourse, define jargon once, no narrative hooks. Skills load independently and do not auto-inherit, so apply these while drafting, or run `humanize-prose` as a final pass.

## Related skills

`tighten-prose` (specialist condensation), `abstract` (research abstract), `highlights` (pointer list), `humanize-prose` (de-AI pass, run last). House-style for the journal and weekly-report forms: `AGENTS.md` (`/journal`, `/weekly-reports`).
