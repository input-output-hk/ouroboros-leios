---
name: humanize-prose
description: Revise LLM-drafted prose so it reads as human-written technical writing, removing machine-generated tells while preserving every fact, number, and citation exactly. Use when a draft needs an editorial pass before hand-off, or when a reviewer flags text as sounding like AI.
---

# Skill: Humanize Prose

Revise LLM-drafted prose so it reads as human-written technical writing, removing the patterns that mark text as machine-generated while preserving every fact, number, and citation exactly. Built for this repository's assessments, reports, notes, and briefs. The target register is set by the document's class in the reader table in [`reader-audit`](../reader-audit/SKILL.md) § Document classes and their readers; a lightly technical audience is the default when no class applies.

This skill is self-contained instructions only. It runs no scripts and fetches nothing, so it carries no supply-chain exposure. Its substance is drawn from public references (see Sources) and aligned to this repo's own conventions in [AGENTS.md](../../../AGENTS.md); it does not import any third-party skill.

## When to Use

- An LLM-drafted document (assessment, weekly or technical report, note, brief) needs an editorial pass before hand-off or review.
- As the prose dimension of a quality check on a document.
- When a reviewer flags text as "sounding like AI" and wants it fixed without changing the technical content.

Do **not** use it to:

- Restructure an append-only log entry. Journal entries, `design-history.md`, and `lessons-learned.md` are historical records; use this skill on them only for vocabulary cleanup in an entry being drafted now, never on a committed one.
- Touch code, data files, or direct quotations.
- Chase an AI-detector score. The goal is clear human-sounding technical prose, not evading a classifier.

## Target register: who we are writing for

The reader is set by the document's class in the reader table in [`reader-audit`](../reader-audit/SKILL.md) § Document classes and their readers. When no class applies, default to a **lightly technical** reader: comfortable with the subject area but not a specialist in every sub-topic, and reading to understand and act, not to be impressed. Do not push a document below its class register; an assessment written for expert readers stays dense, with only Leios-specific terms defined. Write for the class's reader.

- **Plain declarative sentences.** Short to medium length. One idea per sentence. Break a sentence that carries two clauses joined by a dash or semicolon into two.
- **Define jargon and expand acronyms on first use.** A specialist term is fine once introduced; an undefined one loses the reader.
- **Concrete over abstract.** Prefer the specific mechanism, number, or example to a general characterization of it.
- **Neutral, not promotional and not casual.** This is not marketing copy (no hype, no second-person "you," no rhetorical questions) and not a blog (no injected personality, no contractions added for flavor, no deliberately unresolved thoughts). For technical and reference writing, plain and neutral *is* the human voice.
- **Not dense-academic either.** Avoid nominalizations and stacked qualifier chains. If a sentence needs to be read twice, rewrite it.

## Technical tone (the middle-ground register)

Target a plain technical register: clear, direct, confident, and precise, the way a competent engineer explains a result to a peer. It rejects two opposite failure modes — academic or stylish prose (personality, hooks, storytelling, vivid flourishes) and bureaucratic or robotic prose (nominalizations, blanket passive, hedge stacks, metadiscourse). The ten adopted rules:

1. **Plain verbs over nominalizations.** "we measured X," not "measurement of X was performed"; "apply is capped," not "a capping of apply occurs." This is the highest-yield clarity move.
2. **Active voice by default.** Use the passive only when the actor is genuinely irrelevant or unknown. "The node applies each transaction twice" over "each transaction is applied twice."
3. **Calibrate confidence with the qualifier, not a hedge stack.** One hedge or none: "roughly 40 tx/s," not "could potentially possibly be around 40."
4. **No evaluative or enthusiasm adjectives.** Drop "powerful," "elegant," "remarkable," "interestingly." Let the result carry the weight.
5. **Concrete and specific over abstract.** Name the mechanism and the number: "the serial committer binds throughput," not "throughput is subject to various architectural constraints." (See also the vocabulary and intensifier rules under "What to catch.")
6. **Declarative and direct.** No rhetorical questions, no exhortations, no second-person "you."
7. **Restrained first-person plural, for actions only.** "We measured / we built" is fine and natural; avoid "we believe," "we feel it is important."
8. **Cut metadiscourse and signposting.** Delete "it is worth noting," "as we will see," "importantly." Let headings do the signposting.
9. **Define jargon once, then use it freely.** Neither over-explaining (patronizing) nor leaving it opaque.
10. **No narrative arc or hooks.** State the result up front; do not build suspense or open with an anecdote.

For sentence-level construction, `tighten-prose` § Sentence shape offers a restrained cumulative-sentence default: base clause first, then only the trailing modifiers that earn their place.

## Hard invariants (never violate)

1. **Never introduce or alter a fact, name, number, date, quote, or citation that is not in the source text.** A prose pass must not change what a measurement says. When in doubt, keep the original wording.
2. **Preserve the information, not the shape.** When keeping a fact and mirroring the original structure conflict, the fact wins; restructure freely around it.
3. **American English throughout — enforce actively, not passively.** Convert every British spelling to American (see the conversion checklist under "What to catch"). This applies to prose, comments, and identifiers introduced in this repo. The only exceptions are upstream identifiers and direct quotations, which are preserved as written.
4. **Do not overcorrect.** Some "tells" are just good writing: the word *however*, an occasional list of three that is genuinely three things, standard transition words. Fix patterns that are reflexive or inflated, not every instance.

## Process: three passes

Work in this order. Each pass is cheap to re-run.

**Pass 1 — vocabulary.** Replace inflated or over-used AI words with plain ones (see list below). Prefer the copula: "is / has" over "serves as / stands as / represents / boasts."

**Pass 2 — structure.** Break the structural patterns (below). These are stronger tells than any single word, and the highest-value edits.

**Pass 3 — clarity for the target reader.** Vary sentence length so the rhythm is not uniform. Expand or define anything the class's reader would stall on, no more. Make the author's actual judgment visible in plain declarative form. This is a clarity pass, **not** a casual-voice pass.

## What to catch

### Vocabulary (flag and reconsider, do not blanket-delete)

Over-used AI vocabulary: *delve, leverage, tapestry, testament, pivotal, intricate, nuanced, multifaceted, holistic, underscore, showcase, foster, realm, landscape, boasts, vibrant, garner, seamless, crucial, robust, streamline, facilitate, illuminate*.

Judgment applies in technical writing: some of these carry a precise technical meaning in context (a "robust" protocol, "optimize" a query, "leverage" as a verb where no plainer word fits). Keep the word where it means something specific; cut it where it is decoration. The test: does the word add information, or just tone?

Significance and promotional padding to delete outright: *a testament to, stands as, marks a shift, underscores the importance of, plays a vital role, boasts, renowned, breathtaking, in the heart of.*

### Structural anti-patterns (highest value)

- **Parallel negation:** "Not X, but Y" and "It's not just X, it's Y." The single most recognizable tell. Rewrite as a plain statement of what is true.
- **Reflexive rule of three:** triples of adjectives, examples, or clauses used for rhythm. Use the real number of items. Do not pad to three or trim to three.
- **Rhetorical question and answer:** "So what does this mean? It means..." Delete the question; state the point.
- **Mirror structures and manufactured drama:** balanced "just as X, so too Y" constructions; runs of short fragments for effect.
- **Inline-header bullets:** every bullet opening with a bolded `**Term:**` in running prose. Fine occasionally; a tell when every item does it. Exempt: genuine definition or glossary lists, where a bold lead term followed by its definition is the correct structure, not a tell.
- **Diff-anchored writing:** narrating what changed ("previously X, now Y," "up from," "re-anchored on <date>") instead of stating what is currently true. State the current fact; version history belongs in journals and lessons-learned.
- **Signposting and throat-clearing:** "It is important to note," "let's dive in," "here's what you need to know," "at this point." Delete and start with the content.
- **Generic conclusions:** a closing paragraph that restates the intro without adding anything. Cut it or replace it with a specific takeaway.

### Em dashes

Practical bar: **more than two em dashes in the first ~200 words is a heavy AI fingerprint.** Do not ban them outright in report prose, but demote most. An aside set off by em dashes usually becomes a comma clause, a separate sentence, or a colon when it introduces a list or expansion. Reserve the em dash for a genuine sharp break, used occasionally. Exempt: the em dash or en dash separating a term from its definition in a definition list or glossary entry (`**term** — definition`) is structural, not a prose aside, and does not count toward the bar.

### Metaphorical intensifiers (the "load-bearing" family)

Words and phrases that signal importance without adding information: *load-bearing, first-class, non-trivial, at its core, fundamentally, crucially, importantly, it is worth noting, the real question is, speaks to, at the end of the day.* Fix by deletion or by stating the mechanism instead of the meta-commentary that it matters.

- Before: "the throughput target is aspirational but load-bearing for parameter selection."
- After: "the throughput target drives parameter selection even though it is not yet validated."

### British to American spelling (enforce)

LLM output often drifts into British spelling. Convert on every pass. Common cases:

- `-ise` / `-isation` to `-ize` / `-ization`: organise to organize, optimise to optimize, centralised to centralized, prioritisation to prioritization. (Note the genuine exceptions that end in `-ise` in both variants: *advertise, comprise, exercise, supervise, surprise, compromise.*)
- `-yse` to `-yze`: analyse to analyze, paralyse to paralyze.
- `-our` to `-or`: colour to color, behaviour to behavior, favour to favor.
- `-re` to `-er`: centre to center, metre to meter, fibre to fiber. (Keep discipline-standard units and proper names as written where they are identifiers.)
- `-ce` noun to `-se`: licence to license, defence to defense, offence to offense.
- Doubled `l`: modelling to modeling, labelled to labeled, cancelled to canceled, travelling to traveling.
- `-ogue` to `-og`: **catalogue to catalog** (the American form in prose — noun and verb, including catalogued to cataloged and cataloguing to cataloging); dialogue to dialog only in technical UI/API contexts (keep "dialogue" for conversation).
- Miscellaneous: grey to gray, artefact to artifact, whilst to while, towards to toward (US preference), sceptical to skeptical.

Preserve British spelling only inside a direct quotation or an upstream identifier (a function name, a cited title, a proper noun).

### Machine-artifact tells

- Title Case In Headings (use sentence case: capitalize the first word and proper nouns only).
- Decorative emoji as section markers (the repo's defined semantic and provenance markers are exempt; see [AGENTS.md](../../../AGENTS.md)).
- Curly quotes and curly apostrophes where the surrounding text uses straight ones; keep it consistent.
- Chatbot residue: "I hope this helps," "let me know," "great question," knowledge-cutoff disclaimers.
- Hedging stacks: "could potentially possibly." Choose one hedge or none.

### Accessibility for the target reader

Calibrate to the class's reader: an `assessments/` reader needs Leios-specific terms defined — the block-class abbreviations, stage and pipeline names, bare parameter symbols — but not general distributed-systems or consensus jargon, whereas an `artifacts/` or weekly-report reader needs more.

- Expand each acronym on first use, then use the short form.
- Give a one-line plain-language gloss for a specialist term the first time it appears, if the reader would not know it.
- Where a claim rests on a number, keep the number and, if space allows, one word on what it is relative to.

## House-style alignment

This skill enforces, and must not contradict, the repository conventions:

- **American English** and **no hard-wrapping** of Markdown prose ([AGENTS.md](../../../AGENTS.md)).
- **Minimize GitHub ticket references** in analytical and outward-facing documents; name the mechanism, document, or result instead. Where an upstream ticket must be cited, qualify it with its repository.
- **Reference other documents by Markdown hyperlink**, not bare backticks.
- **Name the layer.** A claim about Leios says whether it concerns the paper, the formal specification, a simulator, an implementation, or a deployed network. Do not smooth away a layer qualifier as though it were a hedge.
- The repo's **semantic and provenance markers** are intentional and are not "decorative emoji"; leave them in place ([AGENTS.md](../../../AGENTS.md) § Conventions).

## Modes

State the mode when invoking, or infer from the request:

- **Audit** — report the tells found, with line references and suggested fixes. Change nothing. Use this first on any document you did not draft.
- **Rewrite in place** — apply the edits to the file, then give a short summary of the categories of change (not a diff narration). Use only after an audit, or when the request is explicit.
- **Report-only** — return the revised text without touching files. Use for pasted snippets.

Default to **audit** when unsure.

## What good output looks like

- Every number, name, date, and citation is identical to the source.
- No "not X but Y," no reflexive triples, at most an occasional em dash.
- Headings in sentence case; no throat-clearing openers; no generic closer.
- The document's class reader (see the `reader-audit` reader table) can follow it start to finish without stalling on undefined jargon.
- It reads as though a careful human wrote it plainly, not as though a casual voice was bolted onto a machine draft.

## Sources

Public references this skill is distilled from (for provenance; not fetched at runtime):

- Wikipedia, *Signs of AI writing* — the underlying anti-pattern taxonomy.
- `blader/humanizer` (`SKILL.md`) — 33-pattern taxonomy; the "preserve information, not shape" and "introduce no unsourced fact" invariants.
- `lguz/humanize-writing-skill` — three-pass structure and vocabulary banlist.
- General technical-writing guidance that neutral-plain is the correct human voice for reference and technical text.
