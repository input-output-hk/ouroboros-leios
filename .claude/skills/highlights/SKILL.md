---
name: highlights
description: Produce a bulleted pointer digest where each bullet carries the gist and its hyperlink carries the detail - journal weekly-summaries, release highlights, linked indexes. Use when asked for highlights, a what-shipped list, or a linked index.
---

# Skill: Highlights

Produce a **bulleted pointer digest** for visibility, promotion, or navigation: each bullet a one-line highlight that mostly points to the underlying work rather than reproducing it. The bullet carries the gist and the "so what"; the hyperlink carries the detail. Think release highlights, a journal weekly-summary, a "what shipped" reel, or a linked index. One of four sibling summary skills.

Self-contained instructions only; runs nothing.

## When to Use

- Journal weekly-summary entries.
- Highlight reels for stakeholders or marketing.
- A linked index of deliverables, or slide-ready bullet lists.

Not for: standalone summaries that must convey the result without the link (use `abstract` or `executive-summary`); specialist condensation (use `tighten-prose`).

## Form

- 5 to 7 bullets (more only for a pure index).
- One topic per bullet, one to two sentences.
- Lead with the topic in bold, hyperlinked to the source; then the distilled gist.
- Written so a non-specialist grasps the point. The link is where detail lives.
- Neutral for internal use. For outward-facing or marketing use, stay factual and concrete; let the numbers do the promotion rather than adjectives.

## The pointer discipline

- Each bullet must work as a teaser **and** its link must resolve.
- Do not put a load-bearing number in a bullet that the linked source would contradict; the bullet and its target agree.
- Self-contained on its links, not on unshown context: a reader following only the bullets and their links gets a coherent picture.

## Exemplars

No local exemplars yet — this repository is new. The two forms to link here once they exist: a journal weekly-summary entry under `journal/` whose bullets each link to a section anchor in the corresponding weekly report, and a topic-grouped index of pointers to individual assessment or experiment documents.

## Invariants

Numbers exact; American English; every hyperlink resolves; in outward-facing lists name the thing rather than referencing it by ticket number alone.

## Technical tone

Follow the middle-ground technical register in `humanize-prose` § Technical tone: plain verbs over nominalizations, active voice by default, calibrated confidence over hedge stacks, no evaluative adjectives, concrete over abstract, declarative and direct, restrained first-person-plural, minimal metadiscourse, define jargon once, no narrative hooks. Skills load independently and do not auto-inherit, so apply these while drafting, or run `humanize-prose` as a final pass.

## Related skills

`executive-summary`, `abstract`, `tighten-prose`, `humanize-prose`. House-style for the journal weekly-summary form: `AGENTS.md` (`/journal`, 5-7 bullets hyperlinked to report anchors).
