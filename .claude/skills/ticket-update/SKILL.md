---
name: ticket-update
description: Update custom fields on an existing GitHub issue - Issue Type, sub-issue parent, assignees, ProjectV2 Status, target and start dates - touching only the fields specified. Use when asked to change a ticket's status, parent, assignee, or dates.
---

# Skill: Ticket Update

Update custom fields on an existing GitHub issue: **Issue Type, parent (sub-issue
relationship), assignees, ProjectV2 board Status, Target date, Start date**.
Only the fields you specify are touched; the rest are left as-is. Works against
any repo + ProjectV2 pair; the target for this effort is not yet fixed — see
[`ticket-create`](../ticket-create/SKILL.md) § Board target and pass `--repo` /
`--project` explicitly.

## When to Use

Use this skill when asked to:

- Move a ticket to a different Status column (Backlog → Ready → In progress → Done).
- Set / change a Target date or Start date.
- Change an issue's Type (Task ↔ Bug ↔ Story ↔ ...).
- Add or remove a sub-issue parent relationship.
- Add / replace assignees on an existing issue.
- Bulk field updates ("set these three tickets to `Ready` and Target date 2026-07-17").

Do not use this for creating a new issue — use the `ticket-create` skill for that.

## Usage

```bash
.claude/skills/ticket-update/update-ticket.sh --issue 191 --status "In progress"

.claude/skills/ticket-update/update-ticket.sh --issue 190 \
    --target-date 2026-07-17 \
    --status Ready

.claude/skills/ticket-update/update-ticket.sh --issue 42 --parent 100
.claude/skills/ticket-update/update-ticket.sh --issue 42 --parent none   # remove parent

.claude/skills/ticket-update/update-ticket.sh --issue 42 --assignee bwbush,mfitzi
```

### Flags

| flag | meaning |
|---|---|
| `--issue N` | *required* — issue number to update |
| `--type NAME` | Set Issue Type (`Task`, `Bug`, `Story`, ...) |
| `--parent N` | Set sub-issue parent to #N; or `none` to remove existing parent |
| `--assignee LOGIN[,LOGIN,...]` | Replace assignee list (comma-separated) |
| `--status NAME` | ProjectV2 board Status column |
| `--target-date DATE` | `YYYY-MM-DD`, or `clear` to remove |
| `--start-date DATE` | `YYYY-MM-DD`, or `clear` to remove |
| `--repo OWNER/NAME` | (default: current git repo) |
| `--project N` | (default: first linked ProjectV2) |
| `--dry-run` | Resolve IDs and show what would be changed |
| `--debug` | Verbose GraphQL logging |
| `-h`, `--help` | Show help |

Prints a per-field ✓ or ✗ line for each attempted change.

## How It Works

Each field update is an independent GraphQL mutation. All ID resolutions (Type
name → ID, Status name → option ID, Field name → ID, project detection) are
done at runtime via introspection, not hard-coded. Steps invoked only as needed
by the flags you passed:

- **Type:** `updateIssueIssueType`
- **Parent (set):** `addSubIssue`
- **Parent (remove):** looks up current parent via `issue.parent`, then
  `removeSubIssue` with that parent's ID
- **Parent (replace):** removes current, adds new
- **Assignee:** `updateIssue { assigneeIds }` — replaces the list (this is
  destructive to prior assignees; use with intent)
- **Target date / Start date:** `setIssueFieldValue` with `issueFields:[{fieldId,
  dateValue}]`. These are repo-level Issue Fields, not ProjectV2 fields.
- **Clear a date:** `setIssueFieldValue` with `{fieldId, delete: true}` (deletes
  the field value)
- **Status:** adds the issue to the ProjectV2 board (idempotent) then
  `updateProjectV2ItemFieldValue` with the resolved option ID

If a mutation fails (bad type name, unknown status option, missing issue field),
the script prints the error and continues with the remaining fields. Exit code
is non-zero if any mutation failed.

## Failure Modes

- **Repo has no linked ProjectV2 project** and `--project` isn't provided: the
  script will skip `--status` and warn.
- **Type / Status name doesn't exist**: script prints available options and skips
  that field.
- **Removing a non-existent parent**: `--parent none` on an already-un-parented
  issue is a no-op with a note; not an error.

## Related

- `.claude/skills/ticket-tree/` — read-side companion.
- `.claude/skills/ticket-create/` — create new tickets with fields set in one shot.
