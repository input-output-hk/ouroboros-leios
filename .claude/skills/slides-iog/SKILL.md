---
name: slides-iog
description: Review hand-authored IOG briefing slides for accuracy, precision, completeness, and house style, and draft paste-ready slide text, tables, and SVG graphics for the user to place. Use when the user is building a deck themselves and wants a critic and draftsperson.
---

# Skill: Slides (IOG)

Collaborate with the user on a briefing deck where **the user authors the slides
by hand in Google Slides** and Claude acts as reviewer and draftsperson. The
Drive API, `gslide-mcp`, and pandoc are all unsatisfactory for producing
high-quality *custom* slides, so Claude does not build or edit the deck; instead
it (1) **reviews** slides for accuracy, precision, completeness, and style, and
(2) **suggests** text, tables, and graphics for the user to place. The user is
both author and scribe. Every suggestion is aligned to the IOG briefing house
style captured below, and written in **American English**.

This is distinct from the [`gslide`](../gslide/SKILL.md) skill, which constructs
a deck programmatically through an MCP server. Use `gslide` when the tooling is
wired up and the user wants the deck *built*; use **this** skill when the user
is building the deck themselves and wants a partner to critique and to hand them
paste-ready content.

## When to Use

Invoke when the user asks to:

- Review one or more slides (or a whole deck) for accuracy, precision,
  completeness, or style — typically a briefing or stakeholder deck.
- Draft or improve slide **text** (a headline, a bullet block, a findings pair).
- Draft a slide **table** (delivered as Markdown for import).
- Draft a slide **graphic** (delivered as SVG with a PNG-render command).
- Sanity-check that a slide matches the established IOG briefing look and tone.

## Division of Labor

| Role | Owner | Notes |
|---|---|---|
| Authoring / editing the live deck | **User** | Google Slides, by hand. Claude never edits the deck. |
| Rendering SVG → PNG, importing tables | **User** | Claude supplies the source and the exact command. |
| Reviewing slides | **Claude** | Four dimensions, per-slide, slide-referenced. |
| Drafting text / tables / graphics | **Claude** | Paste-ready, house-style-aligned. |

Do not attempt to write into the deck or to re-enable `gslide-mcp`. If the user
wants direct construction, point them to the `gslide` skill.

## Reading the Current Deck

The user's deck is a Google Slides file. Read it with the **Google Drive
integration** — `read_file_content` (deferred tool
`mcp__claude_ai_Google_Drive__read_file_content`) supports
`application/vnd.google-apps.presentation` and returns per-slide text delimited
by `-----`. Pass the bare presentation ID from the URL
(`.../presentation/d/<ID>/edit`).

- This path is **read-only** — it returns text, not layout, images, or exact
  positioning. It cannot see graphics content, only that a slide has few/many
  text elements. Ask the user to describe a figure if its content matters to a
  review.
- The `gslide-mcp` server is **not wired up in this repository** (it needs a
  GCP project and a browser for OAuth). Do not try `mcp__gslides__*` tools; see
  the [`gslide`](../gslide/SKILL.md) skill if the user wants to set it up.
- If the user exports the deck to **PDF** into the repo (e.g. under
  `artifacts/<deck>/`), read it with the Read tool's `pages` parameter — this
  shows true layout and is the best way to review visual style. **There is no
  reference deck in this repository yet**; ask the user for a PDF export of an
  existing IOG deck the first time house style has to be judged against
  something concrete, and commit it under `artifacts/` as the local reference.

## Two Modes

State the mode when invoking, or infer it from the request. **Default to Review
when unsure** — the user owns the deck, so critiquing what is there is safer than
volunteering content that was not asked for.

### Review Mode

Review the named slides against four dimensions. Report findings **per slide**,
referenced by slide number and/or headline, most-important first. Be a critic,
not a rubber stamp — a clean review is rare and a bare "looks good" is not
useful.

1. **Accuracy** — Is every claim, number, citation, and label true? Cross-check
   load-bearing figures against the corpus: [`facts.md`](../../../facts.md)
   first, then `assessments/`, the experiment `lessons-learned.md` files, and the
   active `journal/` phase log. Flag any number that disagrees with `facts.md`.
   Two repository-specific traps: a figure that has been superseded but is still
   quoted from an older document (check `facts.md` for the current value), and a
   simulator result presented as a property of a deployed network.
2. **Precision** — Is each number regime-labeled (corpus, block size, core
   count, committee size)? Are ranges and `~` used where the evidence is a range?
   Are units correct and dimensionally consistent? Is a ratio re-derivable from
   the numbers on the slide?
3. **Completeness (reader-fit)** — Fix the reader first: the context budget is
   set by the room, not the author. Take the persona from the request, else the
   deck's stakeholder / general-technical reader (see the document-class reader
   table in [`reader-audit`](../reader-audit/SKILL.md)). Against *that* reader, does
   the slide (or the deck's arc) omit anything needed — a defining caveat, a "who
   experiences this" qualifier on a throughput claim, a missing column, a term of
   art or acronym used before it is defined *within the deck* (a repository-wide
   prior definition does not count), assumed cross-document context ("as the
   diffusion experiment showed" with no gloss), an unstated layer (paper,
   specification, simulator, implementation, deployed network), or a dangling
   cross-reference? Is anything promised ("see appendix") actually present?
4. **Style** — Does it match the house style below: headline form, text density,
   fragment-vs-sentence and period practice, punctuation, table structure,
   American spelling, SOW-avoidance?

For prose-heavy slides, you may run the companion content skills as sub-audits:
[`reader-audit`](../reader-audit/SKILL.md) (does the reader in the room have the
scaffolding?), [`tighten-prose`](../tighten-prose/SKILL.md) (is it as short as it
can be?). Report their findings folded into the four dimensions; do not rewrite
the deck.

**Rank and report.** Score each finding **Blocks** (wrong, misleading, or
unreadable — must fix before the room), **Slows** (a reader stumbles but
recovers), or **Minor** (polish). Rank Blocks first. A findings table works well:

| # | Slide | Finding | Dimension | Severity | Suggested fix |
|---|---|---|---|---|---|

Sound the all-clear explicitly per dimension when nothing surfaced — silence is
ambiguous.

### Suggest Mode

Produce paste-ready content, matched to the house style, in the right format for
what the user is placing:

- **Bullets / headline / findings** → plain text or fenced Markdown, so the user
  can paste and let Slides take the formatting. State the intended headline and
  the bullet block separately.
- **Table** → a **Markdown table**. The user renders it in Obsidian or imports it
  into a Google Doc, then transfers it to a slide. Keep it to the column count
  and row density the house style uses (see below). Put code identifiers in
  backticks.
- **Graphic** → an **SVG** written to `artifacts/<deck>/figures/<name>.svg`
  (Google Slides does not accept SVG directly). Provide the exact render command
  the repo uses:

  ```
  magick -density 192 -background white artifacts/<deck>/figures/<name>.svg artifacts/<deck>/figures/<name>.png
  ```

  (`-density 192` = 2× raster; white background for Slides/Slack. PNGs are
  gitignored by convention; the SVG is the source of truth.) Follow the SVG
  gotchas in memory: use real newlines inside `<text>` for line breaks (not
  `\n`); set text alignment via inline `style="…"` or a parent-group attribute,
  because a `<style>` class rule beats a presentation attribute like
  `text-anchor`.

Offer one strong option rather than a menu, but note the trade-off if a genuine
fork exists (e.g. table vs. constellation graphic for the same content).

**Two tests before handing anything over.**
- **So-what** — for each bullet, what does the reader do or understand
  differently? If nothing, cut it or merge it.
- **Stands without the speaker** — a briefing is presented live, but stakeholders
  also read the deck afterward with no narration, so each slide should carry its
  own point unaided. If a slide lands only when spoken to, tighten the slide or
  push the detail into speaker notes.

## House Style (IOG Briefing Conventions)

Distilled from an IOG phase-briefing deck in a sibling engagement. This is the
target for both review and suggestion. No local reference deck exists yet — when
one lands under `artifacts/`, link it here and let it override anything below
that it contradicts.

**Audience.** A general technical blockchain audience — follows consensus and
cryptography but is not expert in any one protocol family, in formal modeling, or
in advanced statistics. Introduce a concept in plain language before relying on
its jargon. Stakeholders are in the room alongside the technical team.

**Headlines.** Short noun phrases, **sentence case** (cap first word only),
**no terminal period**: "Hard constraints", "Consensus design space", "Design
tensions", "Verification budget", "Eight subsystems, fourteen constraints". A
parenthetical qualifier or acronym is fine: "Top 10 findings (only need light
verification)", "Pareto-front mapping (Bayesian optimization)". A small red
eyebrow above the headline tags the section ("Milestone 2", "Phase 2 preview").

**Text density.** Low to moderate. Bullet slides run ~5–8 top-level bullets with
at most one sub-level (`○`). Prefer a table or figure over a dense paragraph;
tables are the workhorse of this deck. Title and section-divider slides carry
almost no text.

**Fragments vs. sentences, and periods.**
- **Headlines** — noun phrase, no period.
- **Label / enumeration bullets** — noun-phrase fragments, capitalized, **no
  period** ("Evidence-based", "High performance Lean 4", "Compiles to WASM").
- **Claim bullets** — complete declarative sentences, **with** a terminal period
  ("No adversarial or tail-latency story.", "GRANDPA cannot be tuned to target;
  it must be replaced."). Keep them terse and confident.
- Table cells that state a claim get periods; short label cells do not.

**Findings framing (the signature move).** State a finding as a **two-part
pair**: a crisp claim, then the load-bearing detail with the numbers. In a table,
that is a "Finding | Detail" (or "Hypothesis | Detail") two-column row:
> **Bytes, not cycles, bottleneck throughput.** | The *N* kB block-size cap
> × ~*M* kB per transaction caps the chain at ~*X* TPS with ~*Y*× CPU headroom
> remaining.

The italic placeholders stand for real, sourced figures — the shape is the point:
claim first in bold, then the arithmetic that makes it checkable on the slide.

**Tables.** The dominant content vehicle. Conventions:
- Black header row, white bold text; left-aligned body cells.
- Bold the row-label / first column when it is a key.
- Code identifiers, module paths, protocol slugs in monospace (`r_block`,
  `MNC.Model.Transaction`, `jolteon`).
- 2–5 columns; enough rows to be complete but readable (the findings tables run
  to 10 rows).
- Common shapes seen: Target | Rationale; # | Item | Detail; Subsystem | Module |
  Role | Constraints; Constraint | Equation | Description; Method | Approach |
  Value; Gap | Description | Closure.
- A controlled **verdict-chip vocabulary** appears as colored pills in some
  tables: AVOID (orange), CONSIDER (green), ANCHOR / STUDY (blue shades). Reuse
  those verbs and colors if a slide sorts candidates by disposition.

**Graphics.** Hand-authored, consistent visual language, one idea each. Types in
the reference deck: a hexagonal design-space radar; "constellation" node diagrams
(six labeled dots, the involved dimensions colored, the rest gray) for
pairwise/triple tensions; an effort-vs-criticality 2×2 scatter; a
reducibility-layer stack; a Sobol heatmap; Pareto parallel-coordinates; a bar
chart; a dendrogram; annotated dashboard screenshots. **Callouts** are blue
rounded boxes with blue text and a blue arrow pointing at the region they label
(e.g. "Inputs", "Constraints", "Violations"). **Asides** — optional notes under a
table — are blue italic, centered ("See appendix for details.", "Note: we'll
likely add the Simplex protocol.").

**Punctuation and numbers.**
- **Em-dash** (spaced " — ") for parenthetical breaks and appositives.
- **En-dash** for numeric ranges: `12–18 s`, `6–9×`, `42–49 TPS`.
- **`×`** for factors/multiplication (`300×`, `~15×`), **`·`** (middle dot) as a
  compact separator and in compound units (`tx·MB/s`, `no chain < 2 s @ > 350
  validators`).
- **`~`** for approximate values.
- Thousands separator comma (`1,000 TPS`, `33.5 M samples`). Space between number
  and unit (`200 kB`, `6 ms`, `5 s`, `8.4 kB`).
- **Always use correct SI prefixes and units.** The kilo prefix is a lowercase
  `k`, so kilobytes is **`kB`** — **`KB` is an error**, always flag and correct
  it. Likewise `MB`, `GB`, `ms`, `µs`, `s`. The reference deck slips to `KB` in
  at least one place (the block-size-cap slide); correct any such slip on sight.
- Code identifiers, protocol names-as-model-labels, and module paths in
  monospace.

**Acronyms and terms of art.** Follow the acronym convention in
[AGENTS.md](../../../AGENTS.md). Define the domain acronyms on first use in the
body (ZK, DA, BFT, DAG, UTxO, TPS, VRF, KES, DDoS, MEV) and the Leios block
classes on first use (IB = input block, EB = endorser block, RB = ranking
block); leave cryptographic scheme names as proper nouns (KZG, PLONK, Groth16,
Nova). Gloss Leios and Cardano terms of art once — stage and pipeline names,
freshest-first delivery, and any bare parameter symbol. On a slide, a first-use
definition can be as light as "Global sensitivity analysis (GSA)".

**Quantitative discipline.** Every load-bearing claim carries a number, a factor,
or an explicit range, and is regime-labeled ("at committees in the hundreds",
"under intercontinental RTT", "at the stated parameterization"). Ratios on a
slide should be re-derivable from the other numbers on that slide. A simulation
result says so on the slide, and names its baseline. This mirrors the standing
project guidance in [AGENTS.md](../../../AGENTS.md) to regime-label every number,
name the layer, and measure the mechanism before naming it.

**Scope-language care.** In stakeholder-facing material prefer "project scope" /
"scope" / "work product" over "SOW" / "Statement of Work" (except in a verbatim
quotation). Carried over from the sibling engagement, where it was a hard client
rule; here it is a default worth keeping unless the user says otherwise.

**Branding chrome (user owns the template; know it for review).** Top-left
"INPUT | OUTPUT GROUP"; butterfly logo top-center; a tagline footer bottom-left
(deck-specific); red section eyebrow above black headline. Title slide: product
name, subtitle, date. A closing "Thank you" slide repeats the resource links. Do
not invent new chrome; flag a slide that departs from it. Confirm the footer
tagline and title-slide subtitle against the user's actual template rather than
assuming this one.

## Exemplars

No local reference deck yet. The recurring slide forms worth reaching for, from
the sibling engagement's briefing deck — link the local instance of each once a
deck exists here:

- **Two-part findings table** — a "Finding | Detail" or "Hypothesis | Detail"
  two-column table, ten rows, split into what is settled versus what still needs
  investigation.
- **Verdict-chip candidate table** — candidates sorted by disposition, with the
  controlled chip vocabulary (AVOID / CONSIDER / ANCHOR / STUDY).
- **Constellation tension diagram** — labeled dots with the involved dimensions
  colored and the rest gray, for pairwise and third-order design tensions.
- **Effort-vs-criticality 2×2 scatter** — for triaging open questions, which is
  the natural form for a scope-discovery deck.
- **Layer stack** — constraints or mechanisms grouped by how reducible they are.
- **Two-column prose + table/figure** — for a design-space or parameter-space
  overview.
- **Equation / constraint table** and a **subsystem map** keyed to it.
- **Annotated screenshot with blue callouts** — for a dashboard, a trace viewer,
  or simulator output.
- **Strengths / Limitations two-column** — the assessment pair.
- **Single-comparison bar chart** — one comparison, large labels.

## Technical Tone and De-AI Catches

Slide text is prose, so the middle-ground technical register in
[`humanize-prose`](../humanize-prose/SKILL.md) § Technical tone applies: plain
verbs over nominalizations, active voice, one hedge or none, no evaluative or
enthusiasm adjectives, no metadiscourse, declarative and direct, no narrative
hooks. Skills do not auto-inherit, so apply these while drafting slide copy, or
run `humanize-prose` as a final pass on a bullet block.

The AI-tells most likely to surface on slides — flag in review, avoid in
suggestions:

- **Parallel negation** ("not X, but Y"; "it's not just X, it's Y") — the most
  recognizable tell. State what is true.
- **Reflexive rule-of-three** — triples padded for rhythm. Use the real number of
  items.
- **Evaluative adjectives** — "powerful", "seamless", "robust" (unless it carries
  a precise technical meaning), "crucial". Let the number carry the weight.
- **Metadiscourse / throat-clearing** — "it is worth noting", "importantly", "at
  its core". Delete it; the headline does the signposting.
- **Diff-anchored writing** — "up from", "previously X, now Y", "re-anchored on
  <date>". A briefing states the current fact; edit history belongs in the journal.
- **Curly / straight quote inconsistency** within a deck.

**Slide-specific exemptions — do not "fix" these.** The house style deliberately
uses forms a prose linter would flag: headline and label bullets are noun-phrase
**fragments**, not full sentences; the two-part findings pair leads with a **bold
term** followed by its detail — that is the exempted definition-list structure,
not an inline-header tell. Sentence-case headlines and terse claim bullets are
the target, not something to expand.

## Invariants

- **Invent nothing.** Every number, name, date, protocol attribution, and
  citation in a suggested slide must be exact and traceable to the corpus
  ([`facts.md`](../../../facts.md), `assessments/`, the experiment
  `lessons-learned.md` files, the active `journal/` phase log). A slide puts a figure on a wall in front of
  stakeholders, so an unsourced or stray number is the highest-damage error this
  skill can make. If a needed figure is not in the corpus, say so and stop — do
  not reconstruct it from memory.
- **Keep every load-bearing caveat.** A regime label, a "who experiences this"
  qualifier, or a scope condition whose removal would let the room draw a
  different conclusion stays on the slide, even under space pressure. Cut words,
  not conditions.
- **American English and SI units** throughout (see House Style).
- **Do not overcorrect.** The intentional slide forms in the Technical Tone
  exemptions above are correct; leave them.
- **Review flags; it does not rewrite the deck.** Claude never edits the live
  deck; suggestions are handed over for the user to place.

## Deliverable Conventions

- **Slide-content fragments live under `artifacts/<deck>/`, not in a scratch/tmp
  dir.** A fragment is the Markdown for one slide (its bullets and/or tables)
  produced in Suggest Mode — save it as `artifacts/<deck>/<topic>.md`,
  self-contained and paste-ready. Lead each with the intended headline (and
  eyebrow) and note which slide it augments. `.md` fragments are tracked.
- Suggested figures live alongside the fragments in `artifacts/<deck>/`. Keep SVG
  sources flat there with a `Makefile` + `.gitignore`. **Ignore only the PNGs
  rendered from a sibling SVG** (build artifacts; regenerate with `make`) — a
  source-of-truth PNG with **no** SVG (e.g. a matplotlib export copied in) stays
  tracked. Give the `Makefile` a `gitignore` target that regenerates that list
  from the SVG set, so adding an SVG needs no manual `.gitignore` edit.
- When suggesting a table, also state which slide it replaces/augments and the
  intended headline.
- Keep a light running record of review findings and open decisions in the
  conversation; if the deck work spans sessions, offer to write a short
  `artifacts/<deck>/review-notes.md`.
- Never suggest `git commit` (leave commits to the user).
