#!/bin/bash
#
# draw-ticket-tree.sh — render a parent/child tree of a GitHub Projects (v2)
# board's tickets, annotated with Status and Target date (due date).
#
# Due dates (Target date / Start date), where a board carries them at all, are
# usually repo-level "Issue Fields" that live on the Issue itself, NOT Projects
# v2 fields. Boards without those fields simply render no dates. They are read
# via the issue's `issueFieldValues` connection and require only the default
# `gh auth login` OAuth token (repo scope) -- no fine-grained token needed.
# See SKILL.md "Reading Target dates" for the query and the trap to avoid
# (projectV2Item.fieldValues returns null for these; that is expected).
#
# If Target date is ever unavailable, the script falls back to an ISO date
# (YYYY-MM-DD) embedded in the ticket title, if any (marked with ~).
#
# Usage:
#   draw-ticket-tree.sh [--owner ORG] [--project N] [--repo OWNER/NAME]
#                       [--all] [--start] [--no-fallback]
#
#   --owner ORG        Project owner login (default: input-output-hk)
#   --project N        Project number. If omitted, auto-detected from the
#                      repo's first linked ProjectV2.
#   --repo OWNER/NAME  Repo whose linked project to auto-detect (default: the
#                      current git repo, via `gh repo view`).
#   --all              Include Done/closed tickets (default: outstanding only).
#   --start            Also show Start date alongside the due date.
#   --no-fallback      Do not infer due dates from ISO dates in titles.
#
set -euo pipefail

OWNER="input-output-hk"
PROJECT=""
REPO=""
INCLUDE_DONE=0
SHOW_START=0
TITLE_FALLBACK=1

while [ $# -gt 0 ]; do
  case "$1" in
    --owner) OWNER="$2"; shift 2 ;;
    --project) PROJECT="$2"; shift 2 ;;
    --repo) REPO="$2"; shift 2 ;;
    --all) INCLUDE_DONE=1; shift ;;
    --start) SHOW_START=1; shift ;;
    --no-fallback) TITLE_FALLBACK=0; shift ;;
    -h|--help) sed -n '2,33p' "$0"; exit 0 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

command -v gh >/dev/null || { echo "gh not found" >&2; exit 1; }
command -v python3 >/dev/null || { echo "python3 not found" >&2; exit 1; }

# --- resolve the project node id -------------------------------------------
if [ -z "$PROJECT" ]; then
  [ -n "$REPO" ] || REPO="$(gh repo view --json nameWithOwner -q .nameWithOwner)"
  RO="${REPO%%/*}"; RN="${REPO##*/}"
  read -r PROJECT_ID PROJECT PROJECT_TITLE < <(gh api graphql -f query="
    query { repository(owner:\"$RO\", name:\"$RN\") {
      projectsV2(first:1) { nodes { id number title } } } }" \
    --jq '.data.repository.projectsV2.nodes[0] | "\(.id) \(.number) \(.title)"')
  [ -n "${PROJECT_ID:-}" ] || { echo "no linked project found for $REPO" >&2; exit 1; }
else
  # number given: try organization then user
  read -r PROJECT_ID PROJECT_TITLE < <(gh api graphql -f query="
    query { organization(login:\"$OWNER\") { projectV2(number:$PROJECT) { id title } } }" \
    --jq '.data.organization.projectV2 | "\(.id) \(.title)"' 2>/dev/null || true)
  if [ -z "${PROJECT_ID:-}" ] || [ "$PROJECT_ID" = "null" ]; then
    read -r PROJECT_ID PROJECT_TITLE < <(gh api graphql -f query="
      query { user(login:\"$OWNER\") { projectV2(number:$PROJECT) { id title } } }" \
      --jq '.data.user.projectV2 | "\(.id) \(.title)"')
  fi
fi
[ -n "${PROJECT_ID:-}" ] && [ "$PROJECT_ID" != "null" ] || { echo "could not resolve project $OWNER/#$PROJECT" >&2; exit 1; }

TODAY="$(date +%F)"

# --- fetch all items (paginated) -------------------------------------------
gh api graphql --paginate -f query="
query(\$endCursor:String) {
  node(id:\"$PROJECT_ID\") {
    ... on ProjectV2 {
      items(first:100, after:\$endCursor) {
        pageInfo { hasNextPage endCursor }
        nodes {
          content {
            __typename
            ... on Issue {
              number title state url parent { number }
              issueFieldValues(first:20) { nodes {
                ... on IssueFieldDateValue { value field { ... on IssueFieldDate { name } } } } }
            }
          }
          status: fieldValueByName(name:\"Status\") { ... on ProjectV2ItemFieldSingleSelectValue { name } }
        }
      }
    }
  }
}" | PROJECT="$PROJECT" PROJECT_TITLE="${PROJECT_TITLE:-}" OWNER="$OWNER" TODAY="$TODAY" \
     INCLUDE_DONE="$INCLUDE_DONE" SHOW_START="$SHOW_START" TITLE_FALLBACK="$TITLE_FALLBACK" \
     python3 -c '
import json, os, re, sys

raw = sys.stdin.read()
dec = json.JSONDecoder()
i, nodes = 0, []
while i < len(raw):
    while i < len(raw) and raw[i].isspace(): i += 1
    if i >= len(raw): break
    obj, i = dec.raw_decode(raw, i)
    nodes += obj["data"]["node"]["items"]["nodes"]

TODAY          = os.environ["TODAY"]
INCLUDE_DONE   = os.environ["INCLUDE_DONE"] == "1"
SHOW_START     = os.environ["SHOW_START"] == "1"
TITLE_FALLBACK = os.environ["TITLE_FALLBACK"] == "1"
ISO = re.compile(r"(\d{4}-\d{2}-\d{2})")

def is_done(status, state):
    s = (status or "").lower()
    return s in ("done", "closed") or state in ("CLOSED", "MERGED")

rows = {}
omitted_prs = 0
for n in nodes:
    c = n.get("content") or {}
    if c.get("__typename") == "PullRequest":
        omitted_prs += 1
        continue  # PRs are not tickets; omit from the tree
    num = c.get("number")
    if num is None:
        continue  # skip draft issues / anything without an issue number
    status = (n.get("status") or {}).get("name")
    # dates live on the ISSUE itself (repo-level Issue Fields), not on the project
    ifv = {}
    for fv in (c.get("issueFieldValues") or {}).get("nodes", []):
        fld = (fv.get("field") or {}).get("name")
        if fld and "value" in fv:
            ifv[fld] = fv["value"]
    target = ifv.get("Target date")
    start  = ifv.get("Start date")
    inferred = False
    if not target and TITLE_FALLBACK:
        m = ISO.search(c.get("title", ""))
        if m:
            target = m.group(1); inferred = True
    rows[num] = dict(
        num=num, title=c.get("title", ""), state=c.get("state"),
        parent=(c.get("parent") or {}).get("number"),
        status=status, target=target, start=start, inferred=inferred,
    )

# choose the working set
if INCLUDE_DONE:
    work = dict(rows)
else:
    work = {k: r for k, r in rows.items() if not is_done(r["status"], r["state"])}

kids = {}
for r in work.values():
    kids.setdefault(r["parent"] if r["parent"] in work else None, []).append(r["num"])

def sort_key(num):
    r = work[num]
    return (r["target"] or "9999-99-99", num)

STATUS_ORDER = {"In progress": 0, "In review": 1, "Ready": 2, "Backlog": 3}

def render(num, depth, prefix, is_last):
    r = work[num]
    connector = "" if depth == 0 else ("└─ " if is_last else "├─ ")
    due = ""
    if r["target"]:
        tag = "~" if r["inferred"] else ""
        overdue = (not is_done(r["status"], r["state"]) and r["target"] < TODAY)
        mark = "  ⚠ OVERDUE" if overdue else ""
        st = "start {} → ".format(r["start"]) if (SHOW_START and r["start"]) else ""
        due = "   ⟨{}due {}{}⟩{}".format(st, tag, r["target"], mark)
    status = "[{}]".format(r["status"] or "-")
    print("{}{}#{} {} {}{}".format(prefix, connector, r["num"], status, r["title"], due))
    ch = sorted(kids.get(num, []), key=sort_key)
    child_prefix = prefix + ("" if depth == 0 else ("   " if is_last else "│  "))
    for j, c in enumerate(ch):
        render(c, depth + 1, child_prefix, j == len(ch) - 1)

roots = sorted(kids.get(None, []), key=sort_key)
title = os.environ.get("PROJECT_TITLE") or ""
print("# {}  (project #{}, owner {})".format(title, os.environ["PROJECT"], os.environ["OWNER"]))
scope = "all tickets" if INCLUDE_DONE else "outstanding tickets"
pr_note = " ({} PR(s) omitted)".format(omitted_prs) if omitted_prs else ""
print("# {} — {} shown{} — as of {}\n".format(scope, len(work), pr_note, TODAY))
for j, root in enumerate(roots):
    render(root, 0, "", j == len(roots) - 1)

# footnotes
n_real = sum(1 for r in work.values() if r["target"] and not r["inferred"])
n_inf  = sum(1 for r in work.values() if r["inferred"])
print()
if n_real == 0 and n_inf > 0:
    print("NOTE: no Target date issue-field values were readable;")
    print("      dates marked ~ are inferred from ISO dates in ticket titles.")
    print("      See SKILL.md \"Reading Target dates\".")
elif n_inf:
    print(f"NOTE: {n_inf} due date(s) marked ~ are inferred from the title, not the Target date field.")
'
