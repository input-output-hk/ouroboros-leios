---
name: qa-afterword
description: Append a structured five-part quality-scrutiny audit to a completed document, covering source retrievability, internal consistency, source fidelity, residual uncertainty, and robustness of conclusions. Use ONLY when the user explicitly asks for a quality-scrutiny pass on a finished document.
---

# Skill: Quality-Scrutiny Afterword

Append a structured quality-scrutiny audit to a completed document, recording where the document stands against retrievable evidence, internal consistency, source fidelity, residual uncertainty, and the robustness of its primary conclusions. The procedure is from [AGENTS.md](../../../AGENTS.md) § Repository Blueprint, under the `/assessments/` entry ("Quality-assessment Afterword").

## When to Use

**Only when the user explicitly asks for a quality-scrutiny pass on a completed document.** Specifically:

- The document is in a state the author considers ready (whether deep dive, weekly report, technical report, assessment, requirement-reconciliation memo, briefing-deck source).
- LLM editing has converged. Human editing has happened (or the author has explicitly waived it).
- The audit is meant to *record* the state, not to drive further drafting.

Do **not** invoke this skill automatically as part of another skill's pipeline. The deep-dive skill, for example, deliberately defers the Afterword to here — chaining the audit into the production pipeline produces a stale snapshot, because the editing pass that follows initial generation will move the surface the audit reports on.

If the user says "quality-check this," "do a QA pass on X," "add an afterword," or similar — invoke. If unclear, ask.

## Output

Appended to the target document **as the last section**, after Sources and after any existing appendices. Heading is exactly:

```markdown
## Afterword: Quality Scrutiny
```

The Afterword has five H3 subsections in the order below. Each subsection records findings; the audit produces a snapshot, not a recommendation list.

## Procedure

Work the five subsections in order. Treat each subsection's heading as a contract: the prose under it must *answer* the heading, not riff on related concerns.

### Subsection 1 — Sources correspond to retrievable URLs

**What to do.** Walk the document's `## Sources` section. For each entry:

1. Identify the URL or relative path.
2. Attempt to fetch it (`WebFetch` for HTTP/HTTPS URLs; `Read` for repo-local paths).
3. Classify as: **Accessible** (200 OK and content matches the title), **Redirected** (final URL differs from cited URL — note both), **Unreachable** (4xx/5xx/timeout), **Paywalled** (access requires authentication), or **Internal** (archival or repo-local; check that the file exists).

**Output.** A short summary: how many entries, how many in each class. Itemize the Unreachable / Redirected / Paywalled cases with the cited URL and the observed status. Accessible entries don't need to be listed individually — a count suffices. *Don't re-cite working URLs; this subsection is for surfacing problems.*

**Common subtleties.**
- Whitepaper PDFs frequently 404 after host migrations; check the maintainer org's current docs site for a new location and record both.
- archive.org snapshots are an acceptable rescue citation if the original is gone; note when used.
- DOI or arXiv ID is more durable than a publisher URL; if the document cites a publisher URL but a DOI/arXiv exists, flag the preference.

### Subsection 2 — Internal consistency

**What to do.** Walk the document looking for:

1. **Numerical contradictions.** The same metric stated two ways (e.g., "~117 validators" in §1.2 and "~150 validators" in §9). Reconcile to a single figure or explicitly note "the source landscape disagrees — see §X."
2. **Cross-reference integrity.** Every `§N`, `§N.M`, `(see §X)`, and `[Title](#anchor)` reference resolves to a real section. Anchor formats vary by renderer — GitHub Markdown uses kebab-case-lower-without-§; pandoc uses a configurable scheme. Check what the document is rendered with.
3. **Conclusion-evidence chain.** The document's headline claims (whatever they are) must trace through stated evidence in the body. If §1.6 says "X is differentiated by Y" and Y doesn't appear in §4–§7, flag it.
4. **Forward-and-back reference symmetry.** A "See §8 Security for the full treatment" in §1.3 implies §8 exists and treats the named topic.

**Output.** Itemize discrepancies. For each, name the two sites in tension and the resolution (or "unresolved — flagged for editorial follow-up"). Sound the all-clear explicitly if nothing was found — silence is ambiguous.

### Subsection 3 — Accuracy against sources

**What to do.** Sample the document's load-bearing factual claims (the headline finding(s), any explicit quotes, any "according to" attributions, any quantitative claim that drives a §12-equivalent conclusion). For each:

1. Open the cited source.
2. Verify the claim is what the source says — not a paraphrase that omits qualifications, not a single sentence lifted from a longer hedge, not a quote that's actually a paraphrase.
3. If the source's claim has caveats the document drops, surface that here.

**Output.** Itemize the claims sampled (~5–10 is appropriate for a deep dive; more for a longer document). For each, classify: **Faithful**, **Paraphrased-with-qualification-lost**, **Paraphrased-presented-as-quote**, or **Exceeds-source**. Don't audit every sentence — that's editing, not scrutiny. Audit the *load-bearing* ones.

**Common subtleties.**
- "X chain achieves N TPS" in marketing copy is *not* a primary source for a deep dive that claims the same TPS — chase to the canonical benchmark.
- Author attributions inside the document ("Authors: A, B, C") should match the cited source's title page exactly, with consistent name order.

### Subsection 4 — Areas of greatest uncertainty

**What to do.** Identify the document's epistemic weak points:

1. **Unsourced claims.** Any quantitative or factual claim without a citation. (If the document uses SCRUTINY markers, those are *acknowledgments* of weakness — list them in summary form here, organized by topic rather than by individual marker. If the marker count is large, name the cluster topics.)
2. **Single-source claims.** Claims where only one source exists and no independent corroboration could be obtained.
3. **Design-intent attributions.** "X was chosen because Y" claims that can't be substantiated without speaking to the original designers; these are often plausible but unverifiable.
4. **Time-sensitive claims.** Anything stated as fact that may have changed since the source was published; flag the source date.

**Output.** A bulleted list of uncertainty clusters, organized roughly by impact on the document's conclusions. Not every unsourced detail — the substantive ones.

### Subsection 5 — Robustness of primary conclusions

**What to do.** Look at the document's headline conclusions (whatever the document is selling — recommendations, ranking, lesson, finding). Ask: *if the uncertainties from Subsection 4 resolve against the document, do the conclusions still hold?*

For each primary conclusion:

1. State it explicitly.
2. Identify which uncertainty clusters (from Subsection 4) bear on it.
3. Assess: **Robust** (conclusion holds even if uncertainties resolve adversely), **Conditional** (conclusion depends on a specific uncertainty resolving favorably; name the dependency), or **Fragile** (conclusion depends on multiple uncertainties resolving favorably; the conclusion should be hedged or supported with additional work).

**Output.** A short table or itemized list of primary conclusions with their robustness classification and the dependencies named. This is the most important subsection — readers who skip to the end should land here.

## Output Format

```markdown
## Afterword: Quality Scrutiny

### Sources correspond to retrievable URLs

[Summary of fetch sweep; itemized problems.]

### Internal consistency

[Discrepancies surfaced or all-clear.]

### Accuracy against sources

[Load-bearing claims sampled and classified.]

### Areas of greatest uncertainty

[Uncertainty clusters bulleted.]

### Robustness of primary conclusions

[Conclusions itemized with Robust / Conditional / Fragile classification and dependencies.]
```

## Conventions

1. **Tone is descriptive, not corrective.** This audit *records* the document's state; it does not edit. Findings stay in the Afterword; any document edits the audit prompts are a separate, subsequent pass.

2. **Provenance marker on the Afterword.** Per the [AGENTS.md](../../../AGENTS.md) provenance markers: 🤖 if LLM-generated, 👱🤖 if human-drafted with LLM refinement, etc. Apply to the Afterword as a whole, in the heading or as a one-line note immediately after the H2.

3. **Don't recreate the document.** The Afterword is bounded to what's in the document plus the sources it cites. New research belongs in a follow-on revision, not in the audit.

4. **American English spelling** throughout, per [AGENTS.md](../../../AGENTS.md).

5. **Length discipline.** A comprehensive Afterword is ~1–3 pages of Markdown for a major document, not 10. The audit's value is in named issues, not exhaustive enumeration.

## Anti-patterns to avoid

- **Auditing while editing.** If the document is mid-revision, abort and ask the user to flag completion. The Afterword is a snapshot.
- **Re-writing weak prose under the guise of QA.** Style edits aren't quality scrutiny — they're editing. Separate passes.
- **Inflating SCRUTINY counts to look thorough.** SCRUTINY markers are the *author's* acknowledgments. The Afterword may summarize them but should not add new ones — that's an editorial intervention.
- **Treating every unsourced claim as critical.** Many unsourced claims are obvious or definitional. Subsection 4 should be selective about what surfaces.
