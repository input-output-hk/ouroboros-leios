---
name: ticket-tree
description: Render a parent/child tree of a GitHub Projects v2 board's tickets annotated with Status and target date, sorted by due date within each parent. Use when asked to show outstanding tickets, summarize the board, or check for overdue work.
---

# Skill: Ticket Tree

Render a parent/child tree of a GitHub Projects (v2) board's tickets, annotated
with each ticket's **Status** and **Target date** (due date), sorted by due date
within each parent. Works against any ProjectV2; the board for this effort is
not yet fixed — see [`ticket-create`](../ticket-create/SKILL.md) § Board target
and pass `--project` explicitly.

## When to Use

Use this skill when asked to:

- Show a tree / outline of outstanding (or all) GitHub tickets and their due dates
- Summarize what is in flight on the project board, grouped by parent issue
- Check for overdue tickets

## Usage

```bash
.claude/skills/ticket-tree/draw-ticket-tree.sh --project N          # outstanding only
.claude/skills/ticket-tree/draw-ticket-tree.sh --project N --all    # include Done
.claude/skills/ticket-tree/draw-ticket-tree.sh --project N --start  # show start dates too
.claude/skills/ticket-tree/draw-ticket-tree.sh                      # auto-detect repo's linked project
```

Flags: `--owner ORG` (default `input-output-hk`), `--project N`, `--repo OWNER/NAME`,
`--all` (include Done/closed), `--start` (show Start date), `--no-fallback`
(disable title-date inference). See the header of the script for details.

Output is a plain-text tree:

```
#12 [In progress] Phase 2 — Protocol Evaluation
└─ #33 [In progress] Phase 2 weekly reports
   ├─ #59 [Ready]   Weekly report — 2026-07-17   ⟨due 2026-07-17⟩
   └─ #60 [Backlog] Weekly report — 2026-07-24   ⟨due 2026-07-24⟩  ⚠ OVERDUE
```

One ticket per line. Roots are tickets whose parent isn't in the shown set;
siblings sort by due date then issue number. Overdue = due date before today and
not Done. **Pull requests on the board are omitted** (the tree is issues only);
the header reports how many PRs were skipped.

## Reading Target dates — where the dates actually live

Where a board carries them at all, **`Target date` and `Start date` are usually
repo-level "Issue Fields"** (GitHub's newer per-issue custom-field feature) — they live on the
**Issue**, not on the Projects v2 board. Read them from the issue's
**`issueFieldValues`** connection. The default `gh auth login` OAuth token
(repo scope) is sufficient — **no fine-grained token required.**

```graphql
query($num: Int!) {
  repository(owner: "input-output-hk", name: "<repo>") {
    issue(number: $num) {
      issueFieldValues(first: 20) {
        nodes {
          __typename
          ... on IssueFieldDateValue {
            value                                # e.g. "2026-07-31" (String, NOT `date`)
            field { ... on IssueFieldDate { id name } }   # union member is IssueFieldDate
          }
        }
      }
    }
  }
}
```

`IssueFieldValue` and its `field` (`IssueFields`) are **unions**, so you must
spread onto concrete members (`IssueFieldDateValue` / `IssueFieldDate`,
`IssueFieldTextValue` / `IssueFieldText`, etc.). The date is the **`value`**
string, not `date`. Target date field id on this repo: **`IFD_kgDNHVU`**.
Write path is `updateIssueFieldValue(input:{issueId, issueField:{fieldId, dateValue:"YYYY-MM-DD"}})` —
note the nested `issueField` object (`dateValue`/`textValue`/`singleSelectOptionId`/`numberValue`);
there is no top-level `fieldId`/`value` (verified 2026-07-24 against the live schema).

**The trap (investigated 2026-07-13):** querying these via the Projects v2 API
(`projectV2Item.fieldValues` / `fieldValueByName("Target date")`) returns
`null`, because the values aren't on the project — the board just *displays* the
issue-level field. That null is expected, not a permissions problem. The
mutation error that confirms it: *"Issue field values cannot be updated using
the updateProjectV2ItemFieldValue mutation, they must be updated using the
updateIssueFieldValue mutation."*

The script reads dates from `content { ... on Issue { issueFieldValues } }`
nested inside the project item, so a single query gets structure + status
(project) and dates (issue). If a date is ever missing it falls back to an ISO
date embedded in the title, marked with a leading `~`.

## Implementation notes

- Pure `gh` + `python3`; no extra deps. Shebang is `#!/bin/bash` (this container
  has `/bin/bash` but no `/usr/bin/env`).
- Paginates ProjectV2 items with `gh api graphql --paginate`; the python reader
  concatenates the multiple JSON pages `--paginate` emits.
- `--project N` resolves the node id via `organization(login).projectV2(number)`,
  falling back to `user(login).projectV2`. With no `--project`, it auto-detects
  the current repo's first linked ProjectV2.
