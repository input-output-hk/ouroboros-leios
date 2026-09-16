---
name: gslide
description: Build a Google Slides deck programmatically through the gslide-mcp MCP server, constructing layout from explicit API calls rather than converting from Markdown. Use when asked to build, extend, or revise a Google Slides deck and the MCP server is available.
---

# Skill: Google Slides Deck via `gslide-mcp`

Build a Google Slides deck programmatically through the [`gslide-mcp`](https://github.com/jemmanuele/gslide-mcp) MCP server, so layout is *constructed* from explicit API calls rather than *converted* from Markdown via pandoc. The skill assumes the MCP server is already wired up and authenticated. **The setup experiment has not been ported into this repository** — see Setup, OAuth, and troubleshooting below for what to do about that.

## When to Use

Invoke when the user asks to build, extend, or revise a Google Slides deck — typically a briefing deliverable or a stakeholder review deck — and they want the deck constructed from a per-slide outline rather than imported from Markdown.

If the user asks for a deck and `gslide-mcp` is *not* available in the session, stop: setting it up needs a GCP project, an OAuth client, and a Claude Code restart, which is the user's call and not something to attempt mid-task. Don't substitute pandoc — that pipeline has known import-time layout breakage, which is the whole reason this tooling exists.

## Inputs

- **Subject and audience** — what the deck is for, who's in the room, how long the slot is.
- **Outline** — a per-slide plan (title, 3–5 key bullets, figure intent, source link, optional speaker notes). If one doesn't exist, the skill's first job is to draft it; see *Workflow Patterns* below.
- **Companion source** (optional) — a technical report, assessment, or design doc the deck summarizes. The deck should cross-link to it (e.g. via GitHub `blob/main/...` URLs once the repo is public) rather than restate.
- **Branding / template** (optional) — an existing IOG-branded deck whose look the new deck should adopt. Use `build_template_library` to ingest, `assemble_from_template` to compose against it.

## Output

A folder under `artifacts/<deck-name>/` containing:

- `README.md` — one-pager: audience, length, time budget, workflow choice.
- `outline.md` — per-slide plan. The slide number is in the heading. Figure intent recorded inline; speaker notes either inline (in a `**Speaker notes:**` block) or in the GSlides deck itself.
- `figures/` — briefing-tailored PNG/SVG generated fresh for this deck (less density, larger labels, presentation colour ramps). Source-controlled.
- `deck-url.txt` — URL of the deployed GSlides deck, written once `create_presentation` returns the deck ID.

The deck itself lives in Google Drive (the user's, since each user runs their own OAuth client per the experiment design). The repo holds the *plan*; the deck is the *artefact*.

## Workflow Patterns

The outline carries intent; the deck carries the artefact. Two patterns have been used to drive these to convergence — either is fine, the user typically signals which one.

### Pattern A — Outline-first, then build

The LLM and user iterate on `outline.md` until every slide has a title, claim bullets, figure intent, and source. Only then does the LLM start calling `create_presentation` / `create_slide` / `batch_write_markdown`. Drift between outline and deck is allowed *during* the build pass, but sync back to the outline at major review points (e.g. after a stakeholder rehearsal).

- **Pros.** Cheapest to iterate — text edits in `outline.md` are faster than tearing down and rebuilding slides. The outline doubles as a speaker-notes source and review document.
- **Best when.** Audience is senior, content is contested, or the deck is long enough that whole-deck rework is expensive.

### Pattern B — Outline as scaffold, refine in the deck

The LLM drafts `outline.md` to bullet-skeleton fidelity, then immediately stands the deck up in Google Slides via the MCP tools. Subsequent iteration happens primarily in the deck (with the LLM driving via tool calls and the user reviewing screenshots), with periodic syncs back to `outline.md` so the plan stays current.

- **Pros.** Faster to a finished-looking artefact. Stakeholders can see and react to actual slides, not bullets.
- **Best when.** Audience is familiar with the content, the deck is short, or the visual layout itself is what needs litigation.

The reference build this guidance is distilled from followed Pattern A — outline first (drafted across two sessions), then a single text-heavy build pass that landed all 31 slides into the existing deck.

## gslide-mcp tools — fluent toolkit

The MCP server exposes ~35 tools as `mcp__gslides__*`. The ones that come up most:

| Tool | Use |
|---|---|
| `create_presentation` | New deck. Returns deck ID — record to `deck-url.txt` immediately. |
| `list_slides` / `inspect_slide` | Discover existing slide / element IDs before editing. |
| `create_slide` | New slide at a given index, with optional layout. |
| `create_shape` | Add a `TEXT_BOX`, `ROUND_RECTANGLE`, etc., with explicit point geometry. |
| `batch_write_markdown` | Fill multiple text-bearing shapes in one batchUpdate (preserves bullets, bold, monospace). |
| `set_text` / `write_text_markdown` | Single-shape variants when one-at-a-time is fine. |
| `insert_image` | Image from URL with explicit geometry. Pre-render figures to PNG/SVG in `figures/` and host via a stable URL. |
| `style_text` / `set_fill` / `set_outline` | Visual polish; usually deferred until the template is right. |
| `screenshot` / `screenshot_range` | Render to PNG inline — Claude sees the result without a separate Read. *Always screenshot a slide after building it.* |
| `overlap_check` | Detect layout collisions. *Always run before declaring a slide done.* |
| `build_template_library` | Ingest an existing branded deck into a reusable registry of slide templates. |
| `assemble_from_template` | Compose new decks from the template library. |

Slide and element IDs are persistent within a deck; capture them as you go so subsequent calls don't have to re-discover. Layout coordinates are in **points** (EMU is handled internally) — typical slide is 720 × 405 pt (16:9) or 720 × 540 pt (4:3).

**`create_slide` inserts sequentially.** Each call at `insertion_index=N` puts the new slide at position N and shifts everything else forward. For an ordered batch, call with `insertion_index = first, first+1, …, first+n-1` in sequence. Parallelizing these is unsafe — the order at the API depends on arrival order, not the requested indices.

**There is no rename-presentation tool.** `create_presentation` accepts a title at deck creation; afterwards, the deck title can only be changed in the Slides UI. If a deck has a placeholder title that needs updating after a build, flag it for the user to rename manually.

## Markdown rendering caveats

`batch_write_markdown` and `write_text_markdown` support **bold**, *italic*, monospace `inline code`, and bullet lists (including nested bullets). They do *not* render:

- **Markdown tables.** `| col | col |` syntax passes through as raw pipe-delimited text — the header separator row `|---|---|` shows up as literal `---`. For a small table, render as aligned bullet lines (e.g. `**N = 25 (small)** — 10 Pareto pts · TPS 175 · …`). For a multi-row data table, create a real Google Slides table via the API (out of scope of `batch_write_markdown`; use the underlying batchUpdate `createTable` request or accept that the rendered output won't have grid lines).
- **Headings.** `#` / `##` pass through as literal hash characters. Use a separate title `TEXT_BOX` with **bold** content for slide titles, not in-body headings.
- **Hyperlinks via `[text](url)`.** These render with an underline but the link target is preserved — confirmed working on the title slide of the 2026-06-29 build.
- **Code fences.** Backtick-fenced blocks pass through with backticks visible. Use inline backticks for monospace runs instead.

Verify any non-trivial markdown via `screenshot` before declaring a slide done. The reference build (31 slides) hit the markdown-table gotcha exactly once and caught it via screenshot.

## Quality discipline

After each non-trivial slide, in this order:

1. `screenshot` — visually confirm the slide reads correctly (text fits, no clipping, no surprise default fonts).
2. `overlap_check` — confirm zero overlap warnings.
3. If either fails, fix and re-screenshot. Don't move to the next slide on a broken one.

This loop is the whole reason `gslide-mcp` beats pandoc → GSlides import: the LLM can see what it built. Skipping it discards the differentiator.

## Concrete layout — text-heavy first draft

For first-draft slides where text density is acceptable (the build pass before the slide-by-slide refinement pass), a two-shape layout per slide produces clean output on a 720 × 405 canvas without any template work:

| Shape | Geometry (`x, y, w, h` in pt) | Use |
|---|---|---|
| Title `TEXT_BOX` | `30, 20, 660, 50` | Slide title in **bold** via `batch_write_markdown`. |
| Body `TEXT_BOX` | `30, 85, 660, 300` | Body content: bullets, headlines with bold lead phrases, short paragraphs. |

Both with `no_outline=true`. Default fonts (typically Arial under "Simple Light") render clean black-on-white at this geometry; bold lead phrases, italic emphasis, inline `monospace`, and bullet lists all survive. The reference build used this layout for all 31 slides and `overlap_check` returned zero warnings across all sampled slides.

Refinement-pass layouts (multi-column cards, badges, headers with colour bands, figure-plus-text splits) build on top of this template — but don't optimize the layout until the content has stabilized.

## Conventions

1. **Hosting figures.** Pre-render to PNG/SVG in `figures/`, then host via a stable URL (e.g. GitHub raw if the repo is public; a temporary `placehold.co` URL during smoke-testing; an IOG-controlled object store for production). `insert_image` needs a URL the Google Slides server can fetch — local file paths don't work.

2. **Template library is *not* free.** Default Google "Simple Light" looks acceptable for smoke tests but is wrong for a stakeholder briefing. Ingest an existing IOG-branded deck via `build_template_library` before standing up a production deck.

3. **Per-deck OAuth.** Each user runs their own gslide-mcp instance against their own GCP project — there's no shared client. The deck lives in the *user's* Drive, not a team-shared account. If a shared editor is needed, share the deck from Slides after creation.

4. **Don't substitute pandoc.** Marp is an acceptable parallel tool (PPTX import path) but `gslide-mcp` is the validated default for keeping Google Slides as the rendering target. If `gslide-mcp` fails for an unrecoverable reason, escalate to the user rather than silently falling back.

5. **American English spelling** throughout outline, speaker notes, and deck text, per `AGENTS.md`.

6. **Provenance markers.** Apply standard provenance markers (🤖 / 👱🤖 / 🤖👱) to `outline.md` and (if appropriate) to the deck's title-slide subtitle, per `AGENTS.md`.

7. **Object-ID naming.** Use a predictable scheme that maps slide number → element IDs without needing a lookup. The reference build used `slide_<prefix>_NN` for slides and `<prefix>_NN_<role>` for shapes — e.g. `slide_p1_07`, `p1_07_title`, `p1_07_body`. Predictable IDs let `batch_write_markdown` target many slides in one request without an `inspect_slide` round-trip per slide. Minimum length is 5 chars (Slides API limit). Allowed chars: `[a-zA-Z0-9_-]`, must start with alpha/underscore.

## Anti-patterns to avoid

- **Building slides without screenshotting.** Defeats the whole differentiator. Always screenshot.
- **Letting the deck drift indefinitely from the outline.** The outline is the plan; if the deck materially diverges, sync back. A deck that disagrees with `outline.md` is a maintenance liability.
- **Rebuilding from scratch when a slide doesn't look right.** `set_position` / `set_text` / `set_fill` are cheap; tearing down and re-creating the slide loses element IDs that callers may have captured.
- **Treating the smoke-test deck as production-quality.** The smoke-test pass demonstrated *that the tool works*; it did not demonstrate that the output is briefing-ready without template work. Don't reuse smoke-test stylings for a stakeholder deliverable.

## Setup, OAuth, and troubleshooting

**The setup experiment has not been ported to this repository.** In the sibling repository this lived under `experiments/gslide/` as a README plus the usual `design-history.md` / `lessons-learned.md` pair, covering the setup script, the prerequisite GCP project and OAuth client, and the diagnostic stories for headless OAuth, Google Workspace policy blocks, Testing-mode allowlisting, and the Claude Code MCP-config path.

Until that is ported, the upstream source of truth is the [`gslide-mcp`](https://github.com/jemmanuele/gslide-mcp) repository itself. Whoever sets this up on a new machine should create `experiments/gslide/` here as they go and record what it took — per [AGENTS.md](../../../AGENTS.md), an undocumented setup gets paid for twice. The one diagnostic worth carrying inline is below, because it costs a session to rediscover.

**`invalid_scope: Bad Request` — Claude Code restart is required.** gslide-mcp's `client()` factory is `@functools.lru_cache(maxsize=1)` (in `auth.py:146`). Once the subprocess has cached a `GoogleAPIClient` with stale credentials, *writing a fresh `token.json` to disk is not enough* — the cached object holds the old refresh token in memory and Google rejects refresh attempts on it. The only fix is to exit Claude Code (`/exit` or Ctrl-D) and re-enter; the subprocess respawns and re-reads `token.json` from disk on first call. Confirm the new token works via direct Python before restarting (a one-shot Slides `presentations().get()` call), so that the restart cost is paid against a known-good token. The reference build hit this exact case.
