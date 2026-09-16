#!/bin/bash
#
# create-ticket.sh — create a GitHub issue with custom-field values set
# (Issue Type, parent, assignee, ProjectV2 board Status, Target/Start dates).
# Generic: works against any repo + ProjectV2 pair. Pass --repo / --project
# explicitly until this effort settles on a tracking board (see SKILL.md).
#
# See SKILL.md for the full usage. Runs against the current git repo by
# default, or against --repo OWNER/NAME.
#
set -euo pipefail

# ─── Defaults ────────────────────────────────────────────────────────────
REPO=""
PROJECT=""
TITLE=""
BODY=""
BODY_FILE=""
PARENT=""
TYPE="Task"
ASSIGNEE="bwbush"
STATUS="Ready"
TARGET_DATE=""
START_DATE=""
DRY_RUN=0
DEBUG=0

usage() {
  cat <<EOF
Usage: $0 --title TITLE (--body TEXT | --body-file PATH) [options]

Required:
  --title TITLE
  --body TEXT         Body text as a string
  --body-file PATH    OR: read body from a file (use - for stdin)

Optional (defaults in parens):
  --parent N          Sub-issue parent number
  --type NAME         Issue Type (Task)
  --assignee LOGIN    Assignee (bwbush; use "" for unassigned)
  --status NAME       ProjectV2 board Status column (Ready)
  --target-date DATE  YYYY-MM-DD
  --start-date DATE   YYYY-MM-DD
  --repo OWNER/NAME   (current git repo)
  --project N         (first linked ProjectV2)
  --dry-run           Resolve IDs, don't create
  --debug             Verbose GraphQL logging
  -h, --help
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --title)       TITLE="$2"; shift 2 ;;
    --body)        BODY="$2"; shift 2 ;;
    --body-file)   BODY_FILE="$2"; shift 2 ;;
    --parent)      PARENT="$2"; shift 2 ;;
    --type)        TYPE="$2"; shift 2 ;;
    --assignee)    ASSIGNEE="$2"; shift 2 ;;
    --status)      STATUS="$2"; shift 2 ;;
    --target-date) TARGET_DATE="$2"; shift 2 ;;
    --start-date)  START_DATE="$2"; shift 2 ;;
    --repo)        REPO="$2"; shift 2 ;;
    --project)     PROJECT="$2"; shift 2 ;;
    --dry-run)     DRY_RUN=1; shift ;;
    --debug)       DEBUG=1; shift ;;
    -h|--help)     usage; exit 0 ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 2 ;;
  esac
done

# ─── Validate ────────────────────────────────────────────────────────────
[ -n "$TITLE" ] || { echo "error: --title required" >&2; exit 2; }
if [ -z "$BODY" ] && [ -z "$BODY_FILE" ]; then
  echo "error: --body or --body-file required" >&2
  exit 2
fi
[ -n "$BODY" ] && [ -n "$BODY_FILE" ] && { echo "error: --body and --body-file are mutually exclusive" >&2; exit 2; }

if [ -n "$BODY_FILE" ]; then
  if [ "$BODY_FILE" = "-" ]; then BODY="$(cat)"; else BODY="$(cat "$BODY_FILE")"; fi
fi

command -v gh >/dev/null   || { echo "gh not found" >&2; exit 1; }
command -v jq >/dev/null   || { echo "jq not found" >&2; exit 1; }

dbg() { [ "$DEBUG" -eq 1 ] && printf '  [debug] %s\n' "$*" >&2 || true; }

# ─── Resolve repo ────────────────────────────────────────────────────────
if [ -z "$REPO" ]; then
  REPO="$(gh repo view --json nameWithOwner -q .nameWithOwner)"
fi
RO="${REPO%%/*}"; RN="${REPO##*/}"
dbg "repo: $RO/$RN"

# ─── Resolve project number (auto-detect if empty) ───────────────────────
PROJECT_ID=""
PROJECT_OWNER_LOGIN=""
if [ -z "$PROJECT" ]; then
  # Try the repo's first linked ProjectV2
  read -r PROJECT PROJECT_ID PROJECT_OWNER_LOGIN < <(gh api graphql -f query="
    query { repository(owner:\"$RO\", name:\"$RN\") {
      projectsV2(first:1) { nodes { number id owner { ... on Organization { login } ... on User { login } } } } } }" \
    | jq -r '.data.repository.projectsV2.nodes[0] | "\(.number) \(.id) \(.owner.login)"' 2>/dev/null || echo "  ")
  if [ -z "${PROJECT:-}" ] || [ "$PROJECT" = "null" ]; then
    echo "warning: repo $RO/$RN has no linked ProjectV2; Status will not be set" >&2
    PROJECT=""
  else
    dbg "auto-detected project #$PROJECT (owner: $PROJECT_OWNER_LOGIN)"
  fi
fi

if [ -n "$PROJECT" ] && [ -z "$PROJECT_ID" ]; then
  # User specified --project; look up its ID under org $RO (best guess)
  PROJECT_ID="$(gh api graphql -f query="
    query { organization(login:\"$RO\") { projectV2(number: $PROJECT) { id } } }" \
    | jq -r '.data.organization.projectV2.id // ""')"
  PROJECT_OWNER_LOGIN="$RO"
  if [ -z "$PROJECT_ID" ]; then
    echo "warning: could not resolve project #$PROJECT under org $RO; Status will not be set" >&2
    PROJECT=""
  fi
fi

# ─── Resolve Issue Type ID ───────────────────────────────────────────────
TYPE_ID=""
if [ -n "$TYPE" ]; then
  TYPE_ID="$(gh api graphql -f query="
    query { repository(owner:\"$RO\", name:\"$RN\") {
      issueTypes(first:20) { nodes { id name } } } }" \
    | jq -r --arg t "$TYPE" '.data.repository.issueTypes.nodes[] | select(.name==$t) | .id')"
  if [ -z "$TYPE_ID" ]; then
    echo "warning: issue type '$TYPE' not found in repo; will skip type assignment" >&2
    echo "  available types:" >&2
    gh api graphql -f query="query { repository(owner:\"$RO\", name:\"$RN\") { issueTypes(first:20) { nodes { name } } } }" \
      | jq -r '.data.repository.issueTypes.nodes[].name' | sed 's/^/    /' >&2
  fi
  dbg "type '$TYPE' -> $TYPE_ID"
fi

# ─── Resolve Parent ID ───────────────────────────────────────────────────
PARENT_ID=""
if [ -n "$PARENT" ]; then
  PARENT_ID="$(gh api graphql -f query="
    query { repository(owner:\"$RO\", name:\"$RN\") { issue(number: $PARENT) { id } } }" \
    | jq -r '.data.repository.issue.id // ""')"
  if [ -z "$PARENT_ID" ]; then
    echo "warning: parent #$PARENT not found; will skip parent linkage" >&2
  fi
  dbg "parent #$PARENT -> $PARENT_ID"
fi

# ─── Resolve Issue Field IDs (Target date, Start date) ───────────────────
declare -A ISSUE_FIELD_ID
if [ -n "$TARGET_DATE" ] || [ -n "$START_DATE" ]; then
  while IFS=$'\t' read -r n id; do
    [ -n "$n" ] && ISSUE_FIELD_ID["$n"]="$id"
  done < <(gh api graphql -f query="
    query { repository(owner:\"$RO\", name:\"$RN\") {
      issueFields(first:20) { nodes {
        ... on IssueFieldDate { name id }
        ... on IssueFieldText { name id }
        ... on IssueFieldSingleSelect { name id }
      } } } }" | jq -r '.data.repository.issueFields.nodes[] | "\(.name)\t\(.id)"')
fi

# ─── Resolve Status field + option IDs on the ProjectV2 board ────────────
STATUS_FIELD_ID=""
STATUS_OPTION_ID=""
if [ -n "$PROJECT" ] && [ -n "$STATUS" ]; then
  STATUS_JSON="$(gh api graphql -f query="
    query { node(id:\"$PROJECT_ID\") {
      ... on ProjectV2 {
        field(name:\"Status\") {
          ... on ProjectV2SingleSelectField { id options { id name } }
        }
      } } }")"
  STATUS_FIELD_ID="$(echo "$STATUS_JSON" | jq -r '.data.node.field.id // ""')"
  STATUS_OPTION_ID="$(echo "$STATUS_JSON" | jq -r --arg s "$STATUS" '.data.node.field.options[]? | select(.name==$s) | .id')"
  if [ -z "$STATUS_OPTION_ID" ]; then
    echo "warning: status option '$STATUS' not found on project; will skip status assignment" >&2
    echo "  available:" >&2
    echo "$STATUS_JSON" | jq -r '.data.node.field.options[]?.name' | sed 's/^/    /' >&2
  fi
  dbg "status '$STATUS' -> field=$STATUS_FIELD_ID option=$STATUS_OPTION_ID"
fi

# ─── Dry-run summary ─────────────────────────────────────────────────────
if [ "$DRY_RUN" -eq 1 ]; then
  cat <<EOF
DRY RUN — resolved IDs:
  repo:                 $RO/$RN
  project #:            ${PROJECT:-<none>}
  project ID:           ${PROJECT_ID:-<none>}
  title:                $TITLE
  body bytes:           ${#BODY}
  assignee:             ${ASSIGNEE:-<unassigned>}
  type name -> ID:      $TYPE -> ${TYPE_ID:-<not resolved>}
  parent -> ID:         #${PARENT:-<none>} -> ${PARENT_ID:-<none>}
  target date:          ${TARGET_DATE:-<none>}${TARGET_DATE:+ (field ID: ${ISSUE_FIELD_ID["Target date"]:-<not resolved>})}
  start date:           ${START_DATE:-<none>}${START_DATE:+ (field ID: ${ISSUE_FIELD_ID["Start date"]:-<not resolved>})}
  status:               ${STATUS:-<none>} (field ID: ${STATUS_FIELD_ID:-<none>}, option: ${STATUS_OPTION_ID:-<none>})
EOF
  exit 0
fi

# ─── Create the issue ────────────────────────────────────────────────────
CREATE_ARGS=(--repo "$RO/$RN" --title "$TITLE" --body "$BODY")
[ -n "$ASSIGNEE" ] && CREATE_ARGS+=(--assignee "$ASSIGNEE")
URL="$(gh issue create "${CREATE_ARGS[@]}")"
NUM="${URL##*/}"
echo "created: $URL"

# Fetch the new issue's node ID
ISSUE_ID="$(gh api graphql -f query="
  query { repository(owner:\"$RO\", name:\"$RN\") { issue(number: $NUM) { id } } }" \
  | jq -r '.data.repository.issue.id')"
dbg "issue #$NUM -> $ISSUE_ID"

# ─── Apply custom fields ─────────────────────────────────────────────────
apply_ok=1
try() { # $1: label, $2: query
  local label="$1"; local q="$2"; local out err
  out="$(gh api graphql -f query="$q" 2>&1)" && rc=0 || rc=$?
  if [ $rc -ne 0 ] || echo "$out" | jq -e '.errors' >/dev/null 2>&1; then
    echo "  ✗ $label: failed" >&2
    echo "$out" >&2
    apply_ok=0
    return 1
  fi
  echo "  ✓ $label"
}

# Type
if [ -n "$TYPE_ID" ]; then
  try "type = $TYPE" "mutation { updateIssueIssueType(input:{issueId:\"$ISSUE_ID\", issueTypeId:\"$TYPE_ID\"}) { issue { number } } }"
fi

# Parent
if [ -n "$PARENT_ID" ]; then
  try "parent = #$PARENT" "mutation { addSubIssue(input:{issueId:\"$PARENT_ID\", subIssueId:\"$ISSUE_ID\"}) { subIssue { number } } }"
fi

# Target date (Issue Field)
if [ -n "$TARGET_DATE" ] && [ -n "${ISSUE_FIELD_ID[Target date]:-}" ]; then
  fid="${ISSUE_FIELD_ID[Target date]}"
  try "target date = $TARGET_DATE" "mutation { setIssueFieldValue(input:{issueId:\"$ISSUE_ID\", issueFields:[{fieldId:\"$fid\", dateValue:\"$TARGET_DATE\"}]}) { issue { number } } }"
fi

# Start date (Issue Field)
if [ -n "$START_DATE" ] && [ -n "${ISSUE_FIELD_ID[Start date]:-}" ]; then
  fid="${ISSUE_FIELD_ID[Start date]}"
  try "start date = $START_DATE" "mutation { setIssueFieldValue(input:{issueId:\"$ISSUE_ID\", issueFields:[{fieldId:\"$fid\", dateValue:\"$START_DATE\"}]}) { issue { number } } }"
fi

# Add to project + set Status
if [ -n "$PROJECT_ID" ] && [ -n "$STATUS_OPTION_ID" ]; then
  ITEM_ID="$(gh api graphql -f query="
    mutation { addProjectV2ItemById(input:{projectId:\"$PROJECT_ID\", contentId:\"$ISSUE_ID\"}) { item { id } } }" \
    | jq -r '.data.addProjectV2ItemById.item.id // ""')"
  if [ -n "$ITEM_ID" ]; then
    try "status = $STATUS" "mutation { updateProjectV2ItemFieldValue(input:{projectId:\"$PROJECT_ID\", itemId:\"$ITEM_ID\", fieldId:\"$STATUS_FIELD_ID\", value:{singleSelectOptionId:\"$STATUS_OPTION_ID\"}}) { projectV2Item { id } } }"
  else
    echo "  ✗ status: could not add issue to project" >&2
    apply_ok=0
  fi
fi

echo ""
if [ "$apply_ok" -eq 1 ]; then
  echo "✓ issue created with all requested fields set: $URL"
else
  echo "⚠ issue created but some field assignments failed: $URL" >&2
  exit 1
fi
