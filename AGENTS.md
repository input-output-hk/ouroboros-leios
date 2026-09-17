# Architectural Intelligence Guide

## Project: Ouroboros Leios Exploration and Troubleshooting

This document is the primary context for interpreting the contents of this repository. It defines the strategic objectives, scope, and technical boundaries of this effort, and the conventions every contributor — human or LLM — is expected to follow.

This repository is a **research-and-development exploration workspace**, not a product repository. Nothing here ships. The output is understanding: reproducible experiments, written assessments, and a defensible record of what was tried, what was learned, and what remains unknown.

> [!IMPORTANT]
>
> **Current phase: scope discovery.** As of 2026-09-16 this effort has no fixed workplan. The objectives below are provisional and the repository blueprint describes directories that are created on first use rather than ones that already exist. Treat every scope statement in this document as a hypothesis to be confirmed, narrowed, or discarded — and update this file when it is.

## 🎯 Mission Objectives

### Phase 0 — Scope discovery (current)

1. **Primary goal:** Determine what this effort should actually be. Enumerate the open questions about [Ouroboros Leios](https://github.com/input-output-hk/ouroboros-leios) that are (a) worth answering, (b) answerable with the resources available here, and (c) not already answered by the upstream Leios team. The deliverable is a written scope statement with candidate workstreams, each sized and ranked.
2. **Secondary goal:** Establish a working environment. Get the upstream Leios artifacts — simulators, formal specifications, trace tooling, analysis scripts — building and running locally, and record what that took. A dead end that is documented is a result; an undocumented one will be paid for twice.
3. **Tertiary goal:** Build the team's shared mental model of Leios: its block classes and their roles, its diffusion and voting mechanics, its parameter space, and the failure modes that distinguish it from Praos.

### Phase 1 and beyond — To be defined

Scope, staffing, and deliverables follow from the Phase-0 scope statement. Do not assume a phase structure beyond Phase 0 until that document exists.

### Standing charter — troubleshooting

Independently of phase, this repository is the home for **R&D-level troubleshooting** of Leios: reproducing anomalies, bisecting simulation divergences, explaining surprising trace output, and isolating whether an observed behavior is a protocol property, a specification gap, an implementation bug, or a measurement artifact. Troubleshooting work is first-class and gets the same evidentiary treatment as planned experiments — a reproduction recipe, a `lessons-learned.md` entry, and a 📊 **EVIDENCE** marker tying the conclusion to its data.

## 🎯 Goals and Constraints

### Primary goals

1. **Explain, don't just observe.** A measurement without a mechanism is an anecdote. Every reported number should come with a claim about *why* it has that value, and that claim should be falsifiable.
2. **Reproducibility over volume.** One experiment a colleague can re-run from a clean checkout is worth more than five that live only in a terminal scrollback. Every experiment carries its own build and run instructions.
3. **Separate the protocol from its implementations.** Leios exists as a paper, as one or more formal specifications, and as one or more simulators and node implementations. Findings must state which of these they are about. A simulator artifact is not a protocol property, and a protocol property is not automatically an implementation guarantee.
4. **Quantify the parameter space, don't sample it anecdotally.** Leios behavior depends on a large, interacting parameter set (stage lengths, block-size and rate limits, committee and quorum sizes, network topology and bandwidth). Conclusions should name the region of parameter space they hold in.

### Hard constraints

- **No authority over upstream.** This repository does not own the Leios specification or its reference implementations. Proposed changes go upstream through normal review; nothing here is a decision of record for the protocol.
- **Public-by-default protocol, private-by-exception materials.** Leios is developed in the open. Anything placed in `background/` is the exception and is treated as private/proprietary — see the blueprint below.
- **Small-scale compute by default.** Assume a single workstation unless a cloud budget is explicitly approved. Where a question genuinely requires a geographically distributed multi-node testbed, say so explicitly in the experiment's `design-history.md` rather than substituting a single-machine run and reporting it as if it answered the question. Single-machine "large network" runs measure CPU and scheduler contention, not network consensus behavior.
- **Simulation results are not deployment claims.** Never present simulator output as a statement about mainnet behavior without naming the modeling assumptions that carry the inference.

### Additional requirements and considerations

- **State the baseline.** Leios claims are throughput and latency claims, and throughput and latency claims are meaningless without a comparator. Name it: Praos as deployed, Praos at some parameterization, or a prior Leios variant.
- **Version everything.** Record the upstream commit, simulator version, parameter file, and seed for every run. An unversioned result cannot be defended.
- **Prefer upstream tooling.** Before writing a new simulator, analysis script, or trace parser, look for the upstream one. Divergent tooling produces divergent numbers and costs more to reconcile than it saves.
- **Negative and null results are recorded, not discarded.** They are the main product of a scope-discovery phase.

### Formal-methods workstream

Leios has an Agda specification lineage upstream, and the properties at issue — safety, liveness, and the throughput-under-adversary arguments — are exactly the kind that reward mechanization. Where this repository touches formal methods, the expectations are:

- Flag any safety or liveness claim in prose that would benefit from mechanized proof, and note whether such a proof already exists upstream or in the literature.
- Distinguish clearly between *proved*, *specified but unproved*, *simulated*, and *asserted*.
- Keep executable specifications executable: a specification that no longer typechecks or runs against the current toolchain is a liability, and its breakage should be recorded in `lessons-learned.md`.

## 👥 Project Staff

| Person | Role | Responsibility |
|--------|------|----------------|
| Brian W. Bush (`bwbush`) | Everything | Scope discovery, upstream-artifact survey, experiments and troubleshooting, assessments, and the repository itself |

One person holds every role as of 2026-09-16. Two consequences worth stating rather than leaving implicit:

- **No reviewer.** Nothing here gets a second pair of human eyes by default, so the written record has to carry the scrutiny a reviewer would otherwise provide. That is what the ❓ / ❓🤖 **SCRUTINY** markers, the `facts.md` sourcing discipline, and the append-only experiment logs are for. Use them on your own work, not only on someone else's.
- **Write for the next person, not for today.** Every document should read as though handed to a colleague who has not been in any of the conversations — see the document-class reader table in [`.claude/skills/reader-audit/SKILL.md`](.claude/skills/reader-audit/SKILL.md). Single-author repositories decay into private notation faster than shared ones.

The roles this effort is expected to draw on if and when it is staffed further: researcher (literature and upstream-artifact survey, protocol analysis, knowledge-base curation), prototyper (simulation runs, trace analysis, benchmark harnesses, troubleshooting reproductions), formal-methods engineer (specification reading and mechanization, safety and liveness analysis), and network engineer (diffusion and propagation measurement, topology modeling, bandwidth accounting).

## 📣 Communication

To be established. Record the engagement's Slack channel and stakeholder list here once they are set, in the form `[#channel](URL)` with the workspace named.

## 📋 Key Facts

Verified facts established through this effort are maintained in [`facts.md`](./facts.md). Consult that file for confirmed findings before reasoning from first principles, and add to it whenever something is confirmed rather than leaving the confirmation buried in a journal entry. Each fact carries its date and its source.

## 📂 Repository Blueprint

Directories are created on first use; in the scope-discovery phase most of this is a target layout rather than a current one.

- `/artifacts/`: Miscellaneous notes and work products — slide decks, diagrams, briefs, synthesis documents.
- `/assessments/`: Technical deep-dives into Leios and comparable protocols, and into their applicability to Cardano. Every assessment must include a `## Sources` section at the end with entries in `[Title — Publisher/Context](URL)` format; use `Title — Publisher/Context (internal)` for internal documents without public URLs. Split the sources section into named subsections (e.g., `### General Sources`, `### Protocol Sources`, `### Cardano Sources`) when the source base spans multiple distinct domains.

  **Quality-assessment Afterword:** Only add an `## Afterword: Quality Scrutiny` section when explicitly asked to do so. When asked, append it after all existing content and structure it as five subsections:
  1. **Sources correspond to retrievable URLs** — attempt to fetch each cited URL; note which are accessible, which redirect, and which are unreachable.
  2. **Internal consistency** — verify that the document's claims do not contradict one another and that conclusions follow from the stated evidence.
  3. **Accuracy against sources** — flag paraphrases presented as quotations, omitted qualifications, and claims that go beyond what the sources state.
  4. **Areas of greatest uncertainty** — list unsourced claims, single-source claims, and design-intent attributions that could not be independently verified.
  5. **Robustness of primary conclusions** — assess whether the main conclusions survive the uncertainties identified above.

- `/background/`: **[PRIVATE/PROPRIETARY]** Centralized storage for reference materials, papers, internal roadmaps, and sensitive communications. Nothing in this directory is quoted verbatim into an outward-facing document without checking its distribution status first.
- `/experiments/`: Code spikes, simulation harnesses, trace-analysis scripts, and troubleshooting reproductions. Each experiment subdirectory must contain two append-only files:
  - `design-history.md` — records design decisions and their rationale as the experiment evolves.
  - `lessons-learned.md` — records findings, surprises, and actionable conclusions.

  Both files are append-only: do not edit or delete previous entries. The only permitted modifications to past entries are ~~strikethrough~~ to mark superseded content, or adding a `> [!TIP]` block referencing a later finding. An experiment directory should also carry enough build/run instructions (a `README.md`, a `Makefile`, or both) that a clean checkout can reproduce its results.
- `/journal/`: phase-keyed logs (e.g., `phase-0.md`). Entries are in **reverse-chronological order**: when inserting a new entry, add it as the first H3 under today's H2 section. Horizontal rules (`---`) separate date sections (H2 headings) **only**; never use a horizontal rule within a journal entry. **Weekly summary entries** use a short bulleted list, 5–7 bullets maximum. Each bullet names a *topic or activity area* — not an individual implementation step — written at a level a non-specialist could understand, in neutral tone without asserting conclusions. **A weekly summary in the journal is derived from a longer weekly report**: first write the single-file weekly report in `/weekly-reports/`, then derive the journal bullets by summarizing each H2 as one bullet, hyperlinked to that H2's anchor in the weekly-report file. **Weekly plan entries** follow the same brevity discipline: a single bulleted list of focus items only, no theme/sequencing/risks/deliverables prose. Ticket numbers go at the **end** of each bullet (`Description [#NN].`), obvious recurring items are omitted, and sub-issues nest as indented bullets.
- `/weekly-reports/`: Detailed single-file weekly reports, named by the Friday end-of-week date (e.g., `2026-09-18.md`). One H2 per topic, a one-paragraph description under each, written to be readable on its own.
- `/_templates/`: Reusable semantic-marker snippets for use when authoring documents.
- `README.md` (top level): Human entry point — what this repository is, the current phase, and a question-indexed map of the artifacts. `AGENTS.md` remains the charter.
- `facts.md` (top level): Verified findings, dated and sourced.
- `/.claude/skills/`: Agent skills, ported from the sibling `arc-mn-consensus` study and retargeted here. Four prose skills (`abstract`, `executive-summary`, `highlights`, `tighten-prose`) plus `humanize-prose` and `reader-audit`; `deep-dive` and `qa-afterword` for assessments; `archival-index` for triaging Drive / Confluence / GitHub corpora; `gslide` and `slides-iog` for briefing decks; and `ticket-create` / `ticket-update` / `ticket-tree` for GitHub Projects work. The document-class reader table in [`reader-audit`](.claude/skills/reader-audit/SKILL.md) is the canonical reader definition for this repository and is referenced by the other prose skills; keep it in sync with this blueprint.
- `meta-lessons-learned.md` (top level): Append-only log of project-level lessons about research methodology, document quality, and process gaps — the project-level analog of the per-experiment `lessons-learned.md` files. Update whenever a cross-cutting failure mode or process gap is identified.
- `flake.nix` / `flake.lock`: The Nix development shell. **Inherited from a sibling study and not yet pruned for this effort** — it currently carries a large toolchain (Lean, Rust, Substrate build tooling, Python scientific stack, R) whose relevance to Leios is unestablished. Treat additions the way the existing entries are written: every package gets a comment saying which experiment needs it and why. Removals are welcome once an entry is confirmed unneeded.

## 📝 Conventions

**Spelling.** Use American English throughout this repository (e.g., "color" not "colour", "centralized" not "centralised", "behavior" not "behaviour", "finalized" not "finalised", "utilization" not "utilisation", "catalog" not "catalogue"). This applies to prose, comments, and identifiers introduced in this repo; preserve the spelling of identifiers from upstream code and of direct quotations as written.

**Markdown line width.** Do not hard-wrap prose in Markdown documents to a fixed column limit. Write each paragraph or bullet as a single logical line and let editors and renderers soft-wrap it. Fixed-width hard wrapping makes edits and diffs noisier and reflows badly across viewers; reserve hard line breaks for actual paragraph, list-item, and block boundaries.

**Visual accessibility.** Use colorblind-safe color schemes in plots and UIs — the [Okabe-Ito palette](https://jfly.uni-koeln.de/color/) (sky blue, vermillion, yellow, bluish green, blue, orange, reddish purple) is the established reference and remains distinguishable under the three most common forms of color vision deficiency. Avoid red/green as the sole distinguisher of state. For any color-coded state, include a non-color redundancy (symbol, label, pattern, or position) so meaning survives if color is invisible or stripped.

**Acronyms and abbreviations.** Define every acronym or abbreviation at its first use in each document, then use the short form freely. Because documents are read independently, "already defined elsewhere in the repository" does not count; define it again here. Exempt only terms universally understood outside this project (e.g., CPU, RAM, URL); spell out domain-specific abbreviations — including the Leios block-class abbreviations (IB, EB, RB), and terms such as VRF, KES, DAG, UTxO, TPS, and DA — on first use in each document.

**Reference documents by Markdown hyperlink.** When you refer to another document in this repository, link it with a Markdown hyperlink `[title](relative/path)` so the reader can open it, rather than naming it in bare backticks. Backticks are for showing a literal path or filename as a string; a reference the reader may want to follow is a link. Tooling files under `.claude/`, where relative links are brittle, are exempt.

**Minimize GitHub ticket references.** Avoid referring to GitHub issues or pull requests by number in analytical and outward-facing documents (assessments, synthesis artifacts, reports); name the technique, mechanism, document, or result instead. Ticket references are acceptable in memory-like and progress-tracking documents — the journal, weekly reports, `lessons-learned.md`, experiment `design-history.md`, `meta-lessons-learned.md` — and where a ticket is genuinely the subject. When referencing an upstream ticket, qualify it with its repository (`ouroboros-leios#NN`), since a bare `#NN` here is ambiguous.

**Frozen historical documents.** Weekly reports and journal entries are historical records; do not edit their existing text. Surface a factual correction by adding a `> [!WARNING]` callout at the point of the error, noting the correction and its date, and leave the original wording in place.

**Provenance of numbers.** Any quantitative result in this repository should be traceable to the run that produced it: upstream commit, tool version, parameter file, seed, and machine. Where a number is an estimate rather than a measurement, mark it ❓ **SCRUTINY** (or ❓🤖 if LLM-derived) rather than letting it acquire false authority by repetition.

**Upstream fidelity.** When describing Leios mechanics, prefer the current upstream specification over the paper, and the paper over secondhand summaries — and say which you used. Where they disagree, that disagreement is itself a finding worth a journal entry.

The following semantic markers are used throughout this repository:

- 🧪 **HYPOTHESIS**: A theory or technical assumption about to be tested.
- 📊 **EVIDENCE**: Links specific experimental data or benchmark results to a claim.
- 🛑 **BLOCKER**: High-priority technical hurdle requiring architectural resolution.
- 🏛️ **ADR**: (Architecture Decision Record) Formal marker for a finalized design choice.
- 🛡️ **SPEC**: A specific requirement that an implementation or parameterization must satisfy.
- ⚠️ **RISK**: Potential risk needing consideration and evaluation.
- ❓ **SCRUTINY**: Marks a quantitative estimate or conclusion produced by a human that has not been empirically verified.
- ❓🤖 **SCRUTINY**: Marks a quantitative estimate or conclusion produced by LLM-assisted reasoning, requiring particular scrutiny.

Provenance markers for journal entries and documents:

- ⏳🤖 Generated by an LLM, pending human review.
- 🤖 Generated by an LLM, reviewed by a human.
- 👱🤖 Drafted by a human, collaboratively refined by an LLM.
- 🤖👱 Drafted by an LLM, collaboratively refined by a human.
- Unmarked entries were solely drafted by a human.

The provenance marker on an assessment document is propagated to its journal summary entry.

**Protocol cheatsheet.** `artifacts/leios-cheatsheet.md` is a living reference document, first populated on 2026-09-17 (Leios mechanisms and the protocol-parameter set; the Ouroboros-family, comparators, and baselines sections are still stubs). Update it whenever a Leios mechanism, block class, parameter, or comparable protocol is newly discussed or explored more deeply — including anything mentioned in an assessment, journal entry, or brainstorming document. Each entry must include at least one source link. It is intended as an onboarding resource for new team members, so descriptions should be objective and self-contained.

**Vendored submodules and patches.** If upstream Leios repositories are vendored as git submodules, modifications are **not** committed inside the submodule. They live as tracked `.patch` files re-applied on build, with the patch files — plus the experiment's `Makefile` — as the reproducible source of truth: a submodule reset or a fresh clone must reconstruct the tree from the patches alone. Therefore, whenever you edit a vendored submodule in place, regenerate the corresponding patch in the same change and commit it. Verify patch currency non-destructively with `git apply --reverse --check <patch>` before relying on a patch set, and wire every patch into the experiment's `make patches` target — an unapplied patch silently has no effect. Where a submodule is shared by more than one experiment, each experiment owns a disjoint patch set and all of them must be accounted for on any reset or re-apply.

## ⏳ Timeline

To be determined. The scope-discovery phase has no committed end date. Its one fixed point as of 2026-09-17 is the **scope brainstorm scheduled for 2026-09-21**; the Phase-0 scope statement follows that meeting rather than preceding it.

## 🤖 Persona & Analysis Instructions

When working in this repository, LLM assistants should:

1. **Assume a Senior Systems Architect and Distributed-Systems Researcher role.** Prioritize correctness, safety, and liveness, and apply the "No Free Lunch" principle across throughput, latency, storage, and fault-tolerance trade-offs. Leios buys throughput with structure; the interesting question is always what it pays.
2. **Be explicit about the layer under discussion.** Paper, formal specification, simulator, node implementation, and deployed network are five different objects. Name which one a claim is about, every time.
3. **Maintain traceability.** Link each 🧪 **HYPOTHESIS** in the journal to the code in `/experiments/` that tests it and to the resulting 📊 **EVIDENCE**.
4. **Be formal-methods aware.** Flag claims about safety and liveness that would benefit from mechanized verification, and note where Agda, TLA+, Isabelle, or Coq treatments already exist upstream or in the literature.
5. **Troubleshoot by bisection, not by narrative.** When explaining an anomaly, isolate it — smaller parameter set, fewer nodes, fixed seed, one changed variable — before proposing a mechanism. Record the reduction, not just the conclusion.
6. **Prefer "unknown" to a confident guess.** In a scope-discovery phase, a well-posed open question is a deliverable. Say what would settle it.
7. **Write to `facts.md` when something is confirmed**, and to `meta-lessons-learned.md` when the process itself failed.

## 💬 Useful Prompts

- **Status summary:** "Summarize the last 10 journal entries. List new 🛑 BLOCKER items or 🏛️ ADR entries."
- **Scope status:** "What candidate workstreams have been identified so far, and what is the current ranking and rationale?"
- **Open questions:** "List the open questions about Leios recorded so far, with what evidence would settle each."
- **Reproduction check:** "For each experiment directory, does it record the upstream commit, parameters, and seed needed to reproduce its results?"
- **Landscape:** "What protocols have been assessed as comparators so far? Summarize their throughput and finality properties."

## Instructions specific to particular LLMs

- *Claude*, please read [CLAUDE.md](./CLAUDE.md) for additional instructions.
