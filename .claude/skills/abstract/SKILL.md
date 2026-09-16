---
name: abstract
description: Write a self-contained paper- or report-style abstract (120-200 words) that a broad technical reader can act on without opening the document. Use when asked for an abstract, or for a standalone summary that must travel detached from its source.
---

# Skill: Abstract

Write a self-contained paper- or report-style **abstract**: one or two short paragraphs, roughly 120-200 words, that a broad technical reader can act on without opening the document. More formal than a weekly summary and more self-contained than a tightened claim. One of four sibling summary skills.

Self-contained instructions only; runs nothing.

## When to Use

- The abstract for a report, assessment, or paper.
- A standalone summary that must travel on its own, detached from the document.

Not for: general stakeholder summaries (use `executive-summary`), in-place specialist condensation (use `tighten-prose`), promotional pointer lists (use `highlights`).

## Audience

Broad technical or research reader: precise, but not assumed to know this sub-topic's specifics. Expand acronyms on first use. No citations by number.

## The arc (in order)

1. **Context and what was done** — one sentence.
2. **Setup / the credibility number** — sample size, real vs synthetic, number of regions, bit-exact, whatever establishes trust.
3. **Headline result** — with numbers and units.
4. **What binds / interpretation** — the limiter, the ceiling, what does not move it.
5. **Honest limitation** — what the result does *not* establish. An abstract that omits its limitation is incomplete.

No headings, no bullets, no throat-clearing ("In this work we present"). Bottom line up front; every sentence carries a fact.

## Exemplar

No local exemplar yet — this repository is new. Link the first good one here once written (a report abstract or a weekly-report lead paragraph), and preserve the property that makes one good: the limitation is not a trailing clause but carries its own weight, often the entire second paragraph. For a simulation- or protocol-analysis abstract in this repository, that limitation paragraph is where the modeling assumptions live — which layer the result is about (paper, formal specification, simulator, implementation, deployed network), what parameter region it holds in, and what it therefore does not establish about a deployed network.

## Invariants

Numbers, names, dates, and citations exact; state the limitation; American English; fully self-contained.

## Technical tone

Follow the middle-ground technical register in `humanize-prose` § Technical tone: plain verbs over nominalizations, active voice by default, calibrated confidence over hedge stacks, no evaluative adjectives, concrete over abstract, declarative and direct, restrained first-person-plural, minimal metadiscourse, define jargon once, no narrative hooks. Skills load independently and do not auto-inherit, so apply these while drafting, or run `humanize-prose` as a final pass.

## Related skills

`executive-summary`, `tighten-prose`, `highlights`, `humanize-prose` (de-AI pass, run last).
