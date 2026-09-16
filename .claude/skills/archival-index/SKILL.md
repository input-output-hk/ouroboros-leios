---
name: archival-index
description: Build a triage index of documents in Google Drive, Confluence, or GitHub that are relevant to a research topic, as reviewable Markdown the user can check off. Use when asked to survey, index, or triage an archival corpus for a subject.
---

# Skill: Archival Index

Build a triage index of documents in Google Drive or Confluence relevant to a research topic, in a consistent Markdown format the user can review and check off for further extraction.

## When to Use

Use this skill when asked to:

- Scrape Google Drive for documents related to a topic and produce an index
- Scrape Confluence for pages related to a topic and produce an index
- Scrape one or more GitHub organizations for markdown documents and produce an index (one file per org)
- Re-run an existing index to refresh entries or add new items
- Index any other external knowledge source whose documents the user wants to triage before extracting

The output is a *triage list*, not a curated archive. The user will review the produced index, check the boxes next to entries worth pulling into `/background/`, and then those become the input to a follow-on extraction task.

## Inputs

- **Source**: `drive`, `confluence`, `github`, or a custom source name
- **Topic**: The research subject (e.g., "Leios throughput", "block diffusion measurement")
- **Scope**: For `github`, the organization name(s). For `drive` and `confluence`, the workspace (usually inferred from auth).
- **Known seed documents** (optional): URLs the user already knows about, used as starting anchors
- **Output path**: `artifacts/<source>-index.md` (default — e.g., `artifacts/google-drive-index.md`, `artifacts/confluence-index.md`, `artifacts/<orgname>-github-index.md`)

## Output

A Markdown file at `artifacts/<source>-index.md` with entries grouped by topical relevance. For GitHub, produce **one file per organization** — do not collapse multiple orgs into a single index, since orgs typically have different access levels, scopes, and topical structures.

## Required MCP Connectors

Authentication for Google Drive and Confluence is via the `/mcp` slash command. If the relevant tools are not yet loaded:

1. Call the connector's `authenticate` tool to surface the OAuth prompt
2. Ask the user to run `/mcp` and select the connector
3. After authentication completes, the actual search and read tools become available via `ToolSearch`

### Google Drive

- `mcp__claude_ai_Google_Drive__search_files` — CQL-like query syntax with `title contains`, `fullText contains`, `mimeType`, `modifiedTime`, `owner`, `sharedWithMe`, `parentId`. Supports `and`/`or`/`not`.
- `mcp__claude_ai_Google_Drive__get_file_metadata` — fetch metadata by file ID, including `modifiedTime`, `createdTime`, `owner`, `title`, `mimeType`.
- `mcp__claude_ai_Google_Drive__read_file_content` — fetch a natural-language rendering of the document body (for follow-up extraction, not the initial index).

### Confluence (Atlassian)

- `mcp__claude_ai_Atlassian__search` — Rovo Search; broad keyword search returning pages, blog posts, and Jira issues. Use this first for topical discovery.
- `mcp__claude_ai_Atlassian__searchConfluenceUsingCql` — CQL search with `title`, `text`, `fullText`, `space`, `type`, `creator`, `lastmodified`, `created`, `id`. **Supports `id in (...)` for batched metadata lookups, which is critical for efficient timestamp retrieval.**
- `mcp__claude_ai_Atlassian__getConfluencePage` — fetch a page by ID; returns the body. Avoid this for metadata-only needs — the body adds tens of KB per page.
- `mcp__claude_ai_Atlassian__getAccessibleAtlassianResources` — get the cloud ID (usually only needed once per session).

### GitHub

No MCP connector is available for GitHub. Use the `gh` CLI via Bash. The user must authenticate themselves before this skill can run:

- Have them run interactively in their shell (with the `!` prefix in the Claude Code prompt): `gh auth login --hostname github.com --git-protocol https --with-token` (paste a PAT) or `--web` (browser flow). Confirm with `gh auth status`.
- For SSO-protected orgs, the PAT or device-flow token must be SSO-authorized for each org separately. If queries against a specific org return empty results despite the org being known to have repos, suspect SSO scope.

Useful `gh` and `gh api` patterns:

- **Repo count**: `gh api -X GET "search/repositories?q=org:<ORG>" --jq '.total_count'`
- **List all repos** (paginated): `gh api -X GET "orgs/<ORG>/repos?per_page=100&page=<N>" --jq '.[] | "\(.name) | \(.description // "(no description)") | \(.updated_at[0:10]) | private=\(.private)"'`
- **Discover topical repos**: `gh api -X GET "search/repositories?q=org:<ORG>+<term1>+OR+<term2>+in:name,description" --jq '.items[] | ...'`. **Limit: ≤5 AND/OR/NOT operators per query** — use multiple parallel queries instead of one big one.
- **List markdown files in a repo**: `gh api -X GET "repos/<ORG>/<REPO>/git/trees/HEAD?recursive=1" --jq '.tree[] | select(.type=="blob" and (.path | endswith(".md"))) | .path'`. Note: `.lagda.md` ends in `.md` so will match; if a repo's content is exclusively `.lagda.md` and the filter mysteriously returns nothing, check for case sensitivity or git-tree truncation.
- **Count markdown files (sanity check before listing)**: append `2>/dev/null | wc -l` to the above pipeline.
- **Code search by extension**: `gh search code 'extension:md org:<ORG> "<term>"'` — useful for large orgs (>100 repos) where enumerating every repo is wasteful. Aggregate results by repo and produce per-repo entries.
- **Per-file last-modified date** (expensive — one call per file): `gh api -X GET "repos/<ORG>/<REPO>/commits?path=<path>&per_page=1" --jq '.[0].commit.committer.date'`. Avoid unless the user explicitly asks; use repo `updated_at` as the default date anchor.

Common pitfalls:

- **Git-tree truncation**: GitHub truncates trees over ~100,000 entries. For large monorepos, use the `/contents/<dir>` endpoint per subdirectory instead.
- **`gh api` returning a string error**: `expected an object but got: string ("...")` typically means the tree call resolved to a single file at the root rather than a tree object. Re-fetch with the explicit ref: `repos/<ORG>/<REPO>/git/trees/main?recursive=1` or `.../trees/master?recursive=1`.
- **Empty `.tree[]` filter results**: check that the repo's default branch exists and that the file extension filter matches. For `.lagda.md`, the `endswith(".md")` filter will catch them; for `.mdx` use `endswith(".mdx")` explicitly.

## Process

### Step 1 — Identify the source and authenticate

If the user does not specify a source, ask which one (Drive, Confluence, GitHub, or several). For Confluence, confirm the workspace host (e.g., `input-output.atlassian.net`) — sometimes the user has multiple workspaces accessible. For GitHub, confirm the org name(s) and verify access with `gh auth status`.

If MCP tools for the source are not yet loaded, trigger authentication and let the user know to run `/mcp`. Wait for the system reminder confirming the new tool set is available before proceeding. For GitHub, no MCP exists — direct the user to authenticate `gh` interactively in their shell.

### Step 2 — Anchor on seed documents (if any)

If the user provided seed URLs, fetch their metadata first (Drive `get_file_metadata` or Confluence `getConfluencePage`) so the index has confirmed entries for the known items. This also surfaces the document's `parentId` (Drive) or `ancestors` (Confluence), which can drive sibling discovery.

### Step 3 — Topical search waves

Run **parallel** searches across a coverage matrix. Group queries by topic and issue them in a single tool-call batch (multiple tool calls in the same assistant message). A typical Leios coverage matrix:

- Direct subject terms (e.g., `Leios`, `input block endorser block`, `freshest first`)
- Sibling and predecessor Ouroboros protocols (`Praos Genesis Peras`, `Ouroboros throughput`)
- Adjacent system names (`Narwhal Bullshark Mysticeti`, `Tendermint HotStuff`, `Solana Sui Aptos`)
- Empirical / engineering terms (`block propagation delay`, `block diffusion measurement`, `mempool throughput`, `bandwidth accounting`)
- Simulation and modeling terms (`network simulation topology`, `discrete event simulator`, `parameter sweep`)
- Formal-methods terms (`Agda specification`, `safety liveness proof`, `conformance testing`)
- Operational concerns (`censorship resistance`, `adversarial stake`, `eclipse attack`, `node resource usage`)
- Cardano platform adjacencies (`ledger throughput`, `script budget`, `transaction size limit`)

Adapt the matrix to the topic. Aim for 4–8 parallel queries per wave. **For GitHub, keep each `gh api search/repositories` query under 5 AND/OR/NOT operators** — split larger ORs across parallel calls.

### Step 4 — Handle oversized responses

Search responses can exceed the inline token cap. When a response is persisted to `/home/claude/.claude/projects/-work/.../tool-results/*.txt`, extract titles, IDs, and modification times with `jq` rather than reading the file linearly:

```bash
jq -r '.files[] | "\(.id) | \(.title) | \(.mimeType) | \(.owner // "n/a") | \(.modifiedTime // "n/a")"' <file>
```

### Step 5 — Triage and group

Categorize entries by topical relevance, not by source date. Sections should reflect the *intellectual structure* of the topic. For a consensus engagement, a useful skeleton:

1. Direct subject discovery / requirements
2. Protocol specification and design rationale
3. Sibling and predecessor protocol work (e.g., Praos, Peras, Genesis for a Leios index)
4. Implementation components (simulators, node components, trace tooling)
5. Empirical / benchmark material
6. Formal-methods material (specifications, proofs, conformance suites)
7. Dependent infrastructure (test networks, observability, data pipelines)
8. Related work in adjacent projects and other chains
9. Comparative blockchain material
10. Strategic / product context
11. Other useful pointers

Items that are clearly off-topic (marketing blog posts on unrelated subjects, HR pages, etc.) should be dropped, not included.

### Step 6 — Batch timestamp lookups

**Confluence.** The Rovo `search` tool's response does **not** include modification timestamps. To populate `**Last modified:**` bullets for Confluence entries:

1. Extract all page IDs from the produced index
2. Batch them into CQL queries using `id in (...)` — about 20 IDs per query stays well under any limit
3. Run the batches in parallel
4. Parse the `lastModified` field from each result and convert `"Mon DD, YYYY"` to ISO `YYYY-MM-DD`

**Google Drive.** The `modifiedTime` is already returned in search results — no follow-up call is needed.

**GitHub.** Per-file commit dates require one `commits?path=<path>&per_page=1` call per file (expensive). Default behavior: use the repo's `updated_at` as the date anchor at the **H2 (per-repo) level**, and skip per-file dates. State this caveat in the file preamble. Only fetch per-file dates when the user explicitly asks for them or when the file matters enough to warrant the extra call (e.g., a flagged "Highest priority" item where staleness changes the decision).

### Step 7 — Write the index

Write the file at the output path. Then add a **Provisional Triage Notes** section at the end that lists what to extract first, what is medium priority, what is low priority, and what is *not yet covered* by the searches.

For GitHub indexes: organize by **H2-per-repo** within optional **H1-per-workstream-cluster** groupings. Each repo H2 should include a one-line repo description (from the GitHub `description` field), the repo's `updated_at`, and `Public.` / `Private.` if relevant. List substantive markdown files as checkboxes under the repo, optionally subgrouped by directory (e.g., `### ADRs`, `### Proposals`, `### Consensus`).

### Step 8 — Make all links checkable

Every per-document `Link` bullet must be a Markdown checkbox so the user can mark items for follow-up. Convert any naked bullets to checked-box form.

## Entry Format

### Standard entry (Drive / Confluence)

```markdown
### <Document Title>

- [ ] **Link:** <URL>
- **Space:** <key>             ← Confluence only
- **Owner:** <name>            ← Drive only
- **Author(s):** <names>       ← optional, when notable
- **Attendees:** <names>       ← meeting notes only
- **Date:** <human date>       ← optional document-stated date
- **Last modified:** <YYYY-MM-DD>
- **Abstract / Description:** <1–3 sentences explaining content and why it matters to the topic>
```

Rules:

- **Title** is always an H3 heading
- The first bullet is always the link, formatted as a Markdown checkbox (`- [ ]`)
- **Last modified** is always present and in ISO `YYYY-MM-DD`
- **Description / Abstract** uses `Abstract` for Drive entries (which have a natural document abstract) and `Description` for Confluence entries (which usually have only a snippet to paraphrase)
- Keep descriptions to 1–3 sentences. They are triage hints, not summaries
- Prefer mentioning concrete numerical findings ("73.5× slower at 10 MB vs 0 MB") over generic descriptors ("contains benchmarks")

### GitHub entry — per-repo H2 with per-file checkboxes

For GitHub, each repo is an H2 section. Substantive markdown files are listed as compact checkbox bullets under the repo, with the description inline. This collapses the per-file metadata into a single line and keeps very-large repos legible.

```markdown
## `<org>/<repo>`

Repo description: <one-line description from the GitHub API>.
Repo last updated: <YYYY-MM-DD>
Public. / Private.

### <Optional subgroup, e.g., "ADRs", "Specification", "Consensus components">

- [ ] **[<short title or path>](<URL>)** — <1-sentence description, with **High priority** annotation if warranted>.
```

Notes:

- **Compact links**: use Markdown link syntax `[<text>](<URL>)` rather than `**Link:** <URL>` on its own bullet — GitHub indexes typically have many entries per repo, and one bullet per file is more readable than a multi-bullet block per file.
- **URLs**: use the `https://github.com/<org>/<repo>/blob/HEAD/<path>` form so links survive default-branch renames.
- **Description quality**: aim for one sentence that captures *why* a reviewer should look — e.g., "DDoS prevention for feeless blockspace ADR" beats "ADR file".
- **High-priority flagging**: when a file is clearly a top extraction target, append `**High priority**` and a short reason.
- **Subgroup headings (H3)** within a repo are optional but useful when a repo has clearly distinct content classes (ADRs, proposals, specs, components). Don't subgroup if it adds noise.
- **Boilerplate filter** (always exclude): `CHANGELOG.md`, `CHANGELOG_*.md`, `CODE_OF_CONDUCT.md`, `CONTRIBUTING.md`, `CONTRIBUTORS.md`, `SECURITY.md`, `LICENSE.md`, `NOTICE.md`, anything under `.github/`, anything under `.changeset/`, anything under `node_modules/`, `target/`, `dist/`, `build/`, `coverage/`. For repos with autogenerated API docs, also exclude `docs/api/`.
- **Very large repos** (>500 markdown files, e.g., docs sites, monorepos): do not enumerate every file. Surface the most architecturally-relevant subset by path-prefix filter (`grep -E '(docs/decisions|spec/|architecture|consensus|/README\.md$)'`), then add a deferral entry noting that the rest can be fetched on demand.
- **Failed tree fetches**: if `gh api repos/.../git/trees/HEAD?recursive=1` returns `expected an object but got: string`, leave a `**(deferred)**` placeholder noting the failure and listing it in the "Not yet sampled" section, so the user knows to re-try with a different ref or `/contents/` walk.

### Multi-link entry (related siblings)

When several documents share an entry — e.g., a series of weekly status reports, repeated benchmark studies, or a recurring meeting — collapse them into one entry and put the date inline on each link:

```markdown
### Benchmarking Block Time (Preview) — multiple runs

- [ ] **Link** (modified 2025-05-27): <URL-1>
- [ ] **Link** (modified 2025-05-27): <URL-2>
- [ ] **Link** (modified 2025-05-27): <URL-3>
- **Space:** SID
- **Description:** ...
```

This avoids ambiguity about which date applies to which sibling and keeps the per-link checkbox.

### Compact sibling list

When the siblings really are a long series of near-identical documents (e.g., 9 weekly simulation slide decks), use a compact list under a single descriptive paragraph:

```markdown
### Weekly Simulation Analyses

- **Description:** A series of weekly slide decks analyzing simulation runs. Source of validated assumptions about realistic network conditions.
- [ ] 2025w28 (modified 2025-07-15): <URL>
- [ ] 2025w27 (modified 2025-07-08): <URL>
- [ ] ...
```

## Section and Document Header

Begin the file with:

```markdown
# <Source> Index — <Topic>-Relevant Material

Index of <Source> documents potentially relevant to <topic context>. Generated by <Source> search on <YYYY-MM-DD>.

Items are grouped by topical relevance. Each entry includes title, link, and a brief description. This is a triage list, not a curated archive — the next step is to review the highest-priority items and pull the substantive content into `/background/` as needed.

<source-specific context, e.g., for Confluence: notable space keys and their meaning; for GitHub: total repo count, scope of curation, public/private mix>

---
```

For GitHub, the preamble should additionally state:

- The total repo count in the org
- That the index is **curated** (when an org is large) — and which workstreams or topics drive the selection
- That dates are repo-level `updated_at` unless flagged otherwise
- The boilerplate filter that was applied
- Whether all repos in the org are public or private (or a mix)

## Provisional Triage Notes

End the file with:

```markdown
## Provisional Triage Notes

- **Highest priority for extraction:** <list specific sections / items>
- **Medium priority:** <list>
- **Low priority:** <list>
- **Skipped from this index:** <classes of result that were filtered out, e.g., hundreds of Jira tickets, marketing blog posts>
- **Not yet sampled:** <classes of search not yet attempted, with rationale for what to try next>
```

The "Not yet sampled" bullet is important — it signals to the user what coverage gaps remain, so a follow-up sweep can target them.

## Conventions

1. **American English spelling** throughout (per `CLAUDE.md`).
2. **ISO dates** (`YYYY-MM-DD`) for all `Last modified` fields, even when the source returns `"Mon DD, YYYY"`.
3. **Checkboxes on every per-document link** so the user can mark items for follow-up.
4. **Don't claim a date you don't have.** If the source returns a clearly invalid timestamp (e.g., Drive's `1970-01-01T00:00:01Z` for some upload artefacts), fall back to `createdTime` and label it `(created)`.
5. **Prefer two-step batching** for Confluence timestamp lookups: a Rovo `search` for discovery (which doesn't give timestamps), then a CQL `id in (...)` batch for timestamps.
6. **URL form depends on the source.** For Drive / Confluence indexes, surface URLs as `<https://...>` angle-bracket form on their own bullet, since per-entry blocks are sparse. For GitHub indexes, use Markdown link syntax `[<short title>](<URL>)` inside the checkbox, because per-repo lists are dense and the compact form is more legible.
7. **Don't include Jira issues by default.** They surface in search but are noise relative to Confluence pages and Drive docs. If a Jira issue is genuinely worth flagging, put it in a separate § with prominent labelling.
8. **Preserve any existing checkboxes** when re-running the skill. If the user has marked `[x]` on an entry, do not revert it to `[ ]`.
9. **One file per GitHub org**, not one combined file across orgs. Org-level access, SSO scope, and topical structure differ enough that combining them harms readability.
10. **Repo-level dates by default** for GitHub. Per-file `git log` lookups are too expensive to do unconditionally; state the caveat in the file preamble.

## Quality Targets

- **Topical grouping**, not chronological — the user is scanning by subject
- **Specific descriptions** that mention concrete artifacts (numbers, decisions, people) where the snippet supports them
- **Triage notes at the end** identifying coverage gaps
- **All links checkable** so the user can mark items for extraction
- **All timestamps in ISO format** for sortability
- **No filler entries** — if a search result is off-topic, drop it
