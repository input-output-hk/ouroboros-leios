---
name: ticket-create
description: Create a GitHub issue with all custom fields set in one invocation - Issue Type, sub-issue parent, assignee, ProjectV2 Status, target and start dates. Use when asked to create a ticket, issue, or sub-issue on a repo linked to a ProjectV2 board.
---

# Skill: Ticket Create

Create a GitHub issue with **all custom fields set in a single invocation**:
Issue Type, parent (sub-issue relationship), assignee, ProjectV2 board Status,
Target date, Start date. Works against any repo + ProjectV2 pair; the target for
this effort is not yet fixed (see Board target below).

## Board target (must be confirmed before first use)

**This effort has no tracking board yet.** This repository has no configured git
remote as of 2026-09-16, so there is nothing for the script to auto-detect.
Confirm the target with the user and record it here before filing anything.

Candidate boards under org `input-output-hk`, for reference:

| Project | Title | Notes |
|---------|-------|-------|
| #209 | Leios ARC | Linked to `input-output-hk/ouroboros-leios`. Has Status, Objective, Quarter, Delivery cycle (iteration), Priority, Size. **No `Target date` / `Start date` fields.** |
| #263 | Leios Internal Delivery | Not inspected. |
| #167 | Leios roadmap & activity | Not inspected. |

Two consequences of the field inventory above:

- Pass `--repo` and `--project` explicitly until a default is settled. The
  scripts work against any repo + ProjectV2 pair; they just have nothing to
  guess from here.
- On a board without date fields, the date options are no-ops: the script warns
  and continues rather than failing. Use the board's own scheduling field
  (iteration, quarter) instead, setting it by hand in the UI — these scripts do
  not write iteration fields.

## When to Use

Use this skill when asked to:

- Create a ticket / issue / sub-issue on this repo (or another repo linked to a
  ProjectV2 board).
- Create a Task, Bug, or Story with a specific target date, assignee, and status.
- Add a sub-ticket under a parent issue (e.g., "create a sub-ticket of #166").

Do not use this for updating an existing issue's fields — use the
`ticket-update` skill for that.

## Usage

```bash
.claude/skills/ticket-create/create-ticket.sh \
    --title "TITLE" \
    --body-file /path/to/body.md \
    --parent 166 \
    --type Task \
    --assignee bwbush \
    --status Ready \
    --target-date 2026-07-17
```

Minimal invocation (uses defaults `--type Task --assignee bwbush --status Ready`):

```bash
.claude/skills/ticket-create/create-ticket.sh \
    --title "TITLE" \
    --body "Short body text"
```

### Flags

| flag | default | meaning |
|---|---|---|
| `--title TITLE` | *required* | Issue title |
| `--body TEXT` | one of body flags required | Body text as a string |
| `--body-file PATH` | ... | Body from file (use `-` for stdin) |
| `--parent N` | none | Sub-issue parent number; creates a parent/child link |
| `--type NAME` | `Task` | Issue Type: `Task`, `Bug`, `Story`, etc. (repo-defined) |
| `--assignee LOGIN` | `bwbush` | Assignee login; empty string leaves unassigned |
| `--status NAME` | `Ready` | ProjectV2 board Status column |
| `--target-date DATE` | none | `YYYY-MM-DD` |
| `--start-date DATE` | none | `YYYY-MM-DD` |
| `--repo OWNER/NAME` | auto | Repo to create in (default: current git repo) |
| `--project N` | auto | ProjectV2 number (default: first linked to the repo) |
| `--dry-run` | off | Resolve and print all IDs, don't create |
| `--debug` | off | Verbose GraphQL logging |
| `-h`, `--help` | — | Show help |

Prints the created issue URL on success.

## How It Works

Creating a ticket with custom fields requires ≥ 4 API calls in the current
GitHub CLI + GraphQL surface:

1. **`gh issue create`** — creates the issue with title, body, assignee.
2. **`updateIssueIssueType`** GraphQL mutation — sets Issue Type.
3. **`addSubIssue`** GraphQL mutation — sets parent relationship.
4. **`setIssueFieldValue`** GraphQL mutation — sets repo-level Issue Fields
   (Target date, Start date). These are *repo-level* Issue Fields, not
   ProjectV2 fields (see the memory note in the tree skill's SKILL.md).
5. **`addProjectV2ItemById`** + **`updateProjectV2ItemFieldValue`** — adds the
   issue to the ProjectV2 board (if not already added) and sets the Status.

Each field resolution is done via GraphQL introspection at runtime — Issue
Type IDs, ProjectV2 board IDs, Status option IDs are all fetched by name, not
hard-coded. This keeps the skill working across renames and across repos.

If any of the field mutations fails, the script prints the failure and continues
with the remaining fields. The issue is left in a partial state and the URL is
printed — you can complete the field setup manually or via the `ticket-update`
skill.

## Failure Modes

- **Repo has no linked ProjectV2 project** and `--project` isn't provided: script
  creates the issue and sets Issue Type / parent / dates but skips the Status
  step and warns.
- **Type name doesn't match any repo Issue Type**: script prints the available
  types and skips the type assignment.
- **Status name doesn't match any board Status option**: script prints the
  available options and skips the status assignment.
- **Parent issue doesn't exist**: `addSubIssue` fails with an error message; the
  issue is created but not parented.

## Related

- `.claude/skills/ticket-tree/` — read-side companion (renders a tree of tickets
  with Status and Target date).
- `.claude/skills/ticket-update/` — write-side companion for modifying existing
  tickets' fields.
- Note: where `Target date` and `Start date` exist at all, they are typically
  **repo-level Issue Fields**, not ProjectV2 fields. That is the quirk this
  script's write path relies on, and the reason the dates are set with
  `setIssueFieldValue` rather than `updateProjectV2ItemFieldValue`.
