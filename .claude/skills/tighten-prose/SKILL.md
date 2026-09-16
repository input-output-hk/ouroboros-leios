---
name: tighten-prose
description: Condense dense specialist prose by cutting inessential qualification while preserving technical density and every load-bearing caveat. Use when a passage is correct but over-qualified, and the reader stays a specialist.
---

# Skill: Tighten Prose

Condense **dense specialist prose** by removing inessential qualifications while preserving technical density, precision, and every load-bearing caveat. This does not translate the writing down for a general audience; the reader stays a specialist. It cuts the fat (parenthetical asides, em-dash asides, hedges, restatements), not the muscle (numbers, scope conditions, the regime a result holds in). One of four sibling summary skills.

Self-contained instructions only; runs nothing.

## When to Use

- Tightening an assessment passage, a findings note, an experiment `lessons-learned.md` entry, or any specialist paragraph that is correct but over-qualified.

Not for: general-audience summaries (use `executive-summary`), self-contained abstracts (use `abstract`), pointer lists (use `highlights`).

## The core distinction: essential vs inessential qualification

- **Load-bearing (keep):** a scope condition, the regime a number applies to, or a caveat whose removal would let a specialist draw a materially different conclusion. Test: if cutting it changes what the claim asserts or when it holds, keep it.
- **Inessential (cut):** a parenthetical aside, an em-dash aside, a hedge stack, a "which, as expected, ..." interjection, or a restatement of something already said. Removal leaves the assertion and its conditions unchanged.

When unsure whether a qualification is load-bearing, keep it. Precision outranks brevity here.

## Techniques

- Convert a nested parenthetical into a following sentence (one idea per sentence).
- Delete interjected asides that carry no condition.
- Collapse a hedge stack ("could potentially possibly") to one hedge or none.
- Merge duplicate qualifications.
- Prefer one flowing sentence per idea over a sentence with nested parentheticals and em-dash asides.

## Before and after

- **Cut inessential:** "This result (which, interestingly, we did not initially expect) shows a ~15% gain." becomes "This result shows a ~15% gain."
- **Restructure, keep the content:** "Vote diffusion, which happens on the same overlay as block diffusion (and is therefore subject to the same per-peer bandwidth cap), completes within the stage." becomes "Vote diffusion completes within the stage. It uses the same overlay as block diffusion, so the same per-peer bandwidth cap applies."

## Sentence shape: restrained cumulative style

A gentle default, not a rule. Try leading a sentence with a clear base clause that states the point, then adding only the trailing modifiers that genuinely sharpen or qualify it. Lean toward spare elaboration: favor precision over accumulation, and feel free to drop any modifier that is not earning its place. When a qualification matters enough to deserve emphasis, it often reads better as its own sentence than trailed onto the end. And keep a trailing modifier attached to the subject it actually describes, so it does not dangle.

What usually helps is the restraint, not the structure: most over-qualified specialist prose already has the right base clause and simply trails too much onto it.

## Exemplar and rulebook

The rule set is above; the one-line version is "one flowing sentence per idea beats a sentence with nested parentheticals and em-dash asides." The target register is the dense, precise, minimally qualified voice of an `assessments/` document written for a distributed-systems engineer — see the assessment row of the document-class reader table in [`reader-audit`](../reader-audit/SKILL.md) § Document classes and their readers. No local exemplar yet; link the first assessment passage that hits this register squarely.

**One repository-specific caution.** In this repository the scope condition on a quantitative claim is almost always load-bearing, and it comes in four recurring forms: which layer the claim is about (paper, formal specification, simulator, implementation, deployed network), which parameterization it holds at, which baseline it is measured against, and which upstream commit produced it. Never cut one of those as an aside.

## Invariants

Numbers, names, dates, and citations exact; keep every load-bearing caveat; American English; do **not** translate jargon down (that is `executive-summary`, a different skill).

## Technical tone

Follow the middle-ground technical register in `humanize-prose` § Technical tone: plain verbs over nominalizations, active voice by default, calibrated confidence over hedge stacks, no evaluative adjectives, concrete over abstract, declarative and direct, restrained first-person-plural, minimal metadiscourse, define jargon once, no narrative hooks. Skills load independently and do not auto-inherit, so apply these while drafting, or run `humanize-prose` as a final pass.

## Related skills

`executive-summary`, `abstract`, `highlights`, `humanize-prose`, `reader-audit` (whose reader table sets the register).
