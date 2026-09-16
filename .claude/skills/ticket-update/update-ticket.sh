#!/bin/bash
#
# update-ticket.sh — update custom fields on an existing GitHub issue
# (Issue Type, parent, assignees, ProjectV2 Status, Target/Start dates).
# Only the fields you specify are touched.
#
# See SKILL.md for full usage.
#
set -euo pipefail

# ─── Defaults ────────────────────────────────────────────────────────────
REPO=""
PROJECT=""
ISSUE=""
TYPE=""
PARENT=""      # numeric N or the string "none"
ASSIGNEE=""    # comma-separated
STATUS=""
TARGET_DATE="" # YYYY-MM-DD or "clear"
START_DATE=""  # YYYY-MM-DD or "clear"
DRY_RUN=0
DEBUG=0

# Track whether each field was explicitly requested (empty default != "unset").
SET_TYPE=0; SET_PARENT=0; SET_ASSIGNEE=0; SET_STATUS=0; SET_TARGET=0; SET_START=0

usage() {
  cat <<EOF
Usage: $0 --issue N [field flags...] [options]

Required:
  --issue N

Field updates (any subset):
  --type NAME             Issue Type
  --parent N | none       Set parent to #N, or 'none' to remove
  --assignee LOGIN[,...]  Replace assignee list (comma-separated)
  --status NAME           ProjectV2 board Status column
  --target-date DATE      YYYY-MM-DD or 'clear'
  --start-date DATE       YYYY-MM-DD or 'clear'

Options:
  --repo OWNER/NAME       (default: current git repo)
  --project N             (default: first linked ProjectV2)
  --dry-run               Resolve + report, don't mutate
  --debug                 Verbose GraphQL logging
  -h, --help
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --issue)       ISSUE="$2"; shift 2 ;;
    --type)        TYPE="$2"; SET_TYPE=1; shift 2 ;;
    --parent)      PARENT="$2"; SET_PARENT=1; shift 2 ;;
    --assignee)    ASSIGNEE="$2"; SET_ASSIGNEE=1; shift 2 ;;
    --status)      STATUS="$2"; SET_STATUS=1; shift 2 ;;
    --target-date) TARGET_DATE="$2"; SET_TARGET=1; shift 2 ;;
    --start-date)  START_DATE="$2"; SET_START=1; shift 2 ;;
    --repo)        REPO="$2"; shift 2 ;;
    --project)     PROJECT="$2"; shift 2 ;;
    --dry-run)     DRY_RUN=1; shift ;;
    --debug)       DEBUG=1; shift ;;
    -h|--help)     usage; exit 0 ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 2 ;;
  esac
done

# ─── Validate ────────────────────────────────────────────────────────────
[ -n "$ISSUE" ] || { echo "error: --issue required" >&2; exit 2; }
[[ "$ISSUE" =~ ^[0-9]+$ ]] || { echo "error: --issue must be numeric" >&2; exit 2; }

if [ "$SET_TYPE" -eq 0 ] && [ "$SET_PARENT" -eq 0 ] && [ "$SET_ASSIGNEE" -eq 0 ] && \
   [ "$SET_STATUS" -eq 0 ] && [ "$SET_TARGET" -eq 0 ] && [ "$SET_START" -eq 0 ]; then
  echo "error: no field flags — nothing to do" >&2
  usage >&2
  exit 2
fi

command -v gh >/dev/null || { echo "gh not found" >&2; exit 1; }
command -v jq >/dev/null || { echo "jq not found" >&2; exit 1; }

dbg() { [ "$DEBUG" -eq 1 ] && printf '  [debug] %s\n' "$*" >&2 || true; }

# ─── Resolve repo ────────────────────────────────────────────────────────
if [ -z "$REPO" ]; then
  REPO="$(gh repo view --json nameWithOwner -q .nameWithOwner)"
fi
RO="${REPO%%/*}"; RN="${REPO##*/}"
dbg "repo: $RO/$RN, issue #$ISSUE"

# ─── Fetch issue node ID + current parent (used for --parent none / replace) ─
ISSUE_JSON="$(gh api graphql -f query="
  query { repository(owner:\"$RO\", name:\"$RN\") {
    issue(number: $ISSUE) { id parent { id number } assignees(first:20) { nodes { id login } } }
  } }")"
ISSUE_ID="$(echo "$ISSUE_JSON" | jq -r '.data.repository.issue.id // ""')"
[ -n "$ISSUE_ID" ] || { echo "error: issue #$ISSUE not found in $RO/$RN" >&2; exit 1; }
CURRENT_PARENT_ID="$(echo "$ISSUE_JSON" | jq -r '.data.repository.issue.parent.id // ""')"
CURRENT_PARENT_NUM="$(echo "$ISSUE_JSON" | jq -r '.data.repository.issue.parent.number // ""')"
dbg "issue ID: $ISSUE_ID; current parent: ${CURRENT_PARENT_NUM:-<none>}"

# ─── Resolve project (only if we need --status) ──────────────────────────
PROJECT_ID=""
if [ "$SET_STATUS" -eq 1 ]; then
  if [ -z "$PROJECT" ]; then
    read -r PROJECT PROJECT_ID < <(gh api graphql -f query="
      query { repository(owner:\"$RO\", name:\"$RN\") {
        projectsV2(first:1) { nodes { number id } } } }" \
      | jq -r '.data.repository.projectsV2.nodes[0] | "\(.number) \(.id)"' 2>/dev/null || echo "  ")
  fi
  if [ -n "$PROJECT" ] && [ -z "$PROJECT_ID" ]; then
    PROJECT_ID="$(gh api graphql -f query="
      query { organization(login:\"$RO\") { projectV2(number: $PROJECT) { id } } }" \
      | jq -r '.data.organization.projectV2.id // ""')"
  fi
  if [ -z "$PROJECT_ID" ]; then
    echo "warning: no ProjectV2 board resolved; --status will be skipped" >&2
    SET_STATUS=0
  else
    dbg "project #$PROJECT -> $PROJECT_ID"
  fi
fi

# ─── Resolve Type ID ────────────────────────────────────────────────────
TYPE_ID=""
if [ "$SET_TYPE" -eq 1 ]; then
  TYPE_ID="$(gh api graphql -f query="
    query { repository(owner:\"$RO\", name:\"$RN\") { issueTypes(first:20) { nodes { id name } } } }" \
    | jq -r --arg t "$TYPE" '.data.repository.issueTypes.nodes[] | select(.name==$t) | .id')"
  if [ -z "$TYPE_ID" ]; then
    echo "warning: issue type '$TYPE' not found; --type will be skipped" >&2
    echo "  available:" >&2
    gh api graphql -f query="query { repository(owner:\"$RO\", name:\"$RN\") { issueTypes(first:20) { nodes { name } } } }" \
      | jq -r '.data.repository.issueTypes.nodes[].name' | sed 's/^/    /' >&2
    SET_TYPE=0
  else
    dbg "type '$TYPE' -> $TYPE_ID"
  fi
fi

# ─── Resolve new Parent ID (unless --parent none) ────────────────────────
NEW_PARENT_ID=""
if [ "$SET_PARENT" -eq 1 ] && [ "$PARENT" != "none" ]; then
  [[ "$PARENT" =~ ^[0-9]+$ ]] || { echo "error: --parent must be numeric or 'none'" >&2; exit 2; }
  NEW_PARENT_ID="$(gh api graphql -f query="
    query { repository(owner:\"$RO\", name:\"$RN\") { issue(number: $PARENT) { id } } }" \
    | jq -r '.data.repository.issue.id // ""')"
  if [ -z "$NEW_PARENT_ID" ]; then
    echo "warning: parent #$PARENT not found; --parent will be skipped" >&2
    SET_PARENT=0
  fi
fi

# ─── Resolve Assignee user IDs ──────────────────────────────────────────
declare -a ASSIGNEE_IDS=()
if [ "$SET_ASSIGNEE" -eq 1 ]; then
  IFS=',' read -ra LOGINS <<< "$ASSIGNEE"
  for login in "${LOGINS[@]}"; do
    login="$(echo "$login" | xargs)"
    [ -z "$login" ] && continue
    uid="$(gh api graphql -f query="query { user(login:\"$login\") { id } }" \
      | jq -r '.data.user.id // ""')"
    if [ -z "$uid" ]; then
      echo "warning: user '$login' not found; skipping" >&2
    else
      ASSIGNEE_IDS+=("\"$uid\"")
    fi
  done
fi

# ─── Resolve Issue Field IDs (Target date / Start date) ─────────────────
declare -A ISSUE_FIELD_ID
if [ "$SET_TARGET" -eq 1 ] || [ "$SET_START" -eq 1 ]; then
  while IFS=$'\t' read -r n id; do
    [ -n "$n" ] && ISSUE_FIELD_ID["$n"]="$id"
  done < <(gh api graphql -f query="
    query { repository(owner:\"$RO\", name:\"$RN\") {
      issueFields(first:20) { nodes {
        ... on IssueFieldDate { name id }
        ... on IssueFieldSingleSelect { name id }
      } } } }" | jq -r '.data.repository.issueFields.nodes[] | "\(.name)\t\(.id)"')
fi

# ─── Resolve Status field + option ID on the ProjectV2 board ────────────
STATUS_FIELD_ID=""
STATUS_OPTION_ID=""
if [ "$SET_STATUS" -eq 1 ]; then
  STATUS_JSON="$(gh api graphql -f query="
    query { node(id:\"$PROJECT_ID\") { ... on ProjectV2 { field(name:\"Status\") {
      ... on ProjectV2SingleSelectField { id options { id name } } } } } }")"
  STATUS_FIELD_ID="$(echo "$STATUS_JSON" | jq -r '.data.node.field.id // ""')"
  STATUS_OPTION_ID="$(echo "$STATUS_JSON" | jq -r --arg s "$STATUS" '.data.node.field.options[]? | select(.name==$s) | .id')"
  if [ -z "$STATUS_OPTION_ID" ]; then
    echo "warning: status option '$STATUS' not found on project #$PROJECT; --status will be skipped" >&2
    echo "  available:" >&2
    echo "$STATUS_JSON" | jq -r '.data.node.field.options[]?.name' | sed 's/^/    /' >&2
    SET_STATUS=0
  fi
fi

# ─── Dry-run summary ─────────────────────────────────────────────────────
if [ "$DRY_RUN" -eq 1 ]; then
  cat <<EOF
DRY RUN — resolved:
  issue:         $RO/$RN#$ISSUE ($ISSUE_ID)
  current parent: ${CURRENT_PARENT_NUM:-<none>}
$( [ "$SET_TYPE" -eq 1 ]     && echo "  set type:      $TYPE -> $TYPE_ID" )
$( [ "$SET_PARENT" -eq 1 ]   && ( [ "$PARENT" = "none" ] && echo "  set parent:    <remove existing>" || echo "  set parent:    #$PARENT -> $NEW_PARENT_ID" ) )
$( [ "$SET_ASSIGNEE" -eq 1 ] && echo "  set assignees: [${ASSIGNEE_IDS[*]}]" )
$( [ "$SET_STATUS" -eq 1 ]   && echo "  set status:    $STATUS -> field=$STATUS_FIELD_ID option=$STATUS_OPTION_ID" )
$( [ "$SET_TARGET" -eq 1 ]   && echo "  set target:    $TARGET_DATE (field=${ISSUE_FIELD_ID[Target date]:-<missing>})" )
$( [ "$SET_START" -eq 1 ]    && echo "  set start:     $START_DATE  (field=${ISSUE_FIELD_ID[Start date]:-<missing>})" )
EOF
  exit 0
fi

# ─── Apply mutations ────────────────────────────────────────────────────
apply_ok=1
try() { # $1: label, $2: query
  local label="$1"; local q="$2"; local out
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
if [ "$SET_TYPE" -eq 1 ] && [ -n "$TYPE_ID" ]; then
  try "type = $TYPE" "mutation { updateIssueIssueType(input:{issueId:\"$ISSUE_ID\", issueTypeId:\"$TYPE_ID\"}) { issue { number } } }"
fi

# Parent
if [ "$SET_PARENT" -eq 1 ]; then
  if [ "$PARENT" = "none" ]; then
    if [ -n "$CURRENT_PARENT_ID" ]; then
      try "parent = <remove>" "mutation { removeSubIssue(input:{issueId:\"$CURRENT_PARENT_ID\", subIssueId:\"$ISSUE_ID\"}) { subIssue { number } } }"
    else
      echo "  · parent: already unparented (no-op)"
    fi
  else
    # If already has a parent that isn't the requested one, remove first
    if [ -n "$CURRENT_PARENT_ID" ] && [ "$CURRENT_PARENT_ID" != "$NEW_PARENT_ID" ]; then
      try "parent (remove old)" "mutation { removeSubIssue(input:{issueId:\"$CURRENT_PARENT_ID\", subIssueId:\"$ISSUE_ID\"}) { subIssue { number } } }"
    fi
    try "parent = #$PARENT" "mutation { addSubIssue(input:{issueId:\"$NEW_PARENT_ID\", subIssueId:\"$ISSUE_ID\"}) { subIssue { number } } }"
  fi
fi

# Assignees
if [ "$SET_ASSIGNEE" -eq 1 ]; then
  IDS_LIST=""
  if [ ${#ASSIGNEE_IDS[@]} -gt 0 ]; then
    IDS_LIST="$(IFS=,; echo "${ASSIGNEE_IDS[*]}")"
  fi
  try "assignees = [$ASSIGNEE]" "mutation { updateIssue(input:{id:\"$ISSUE_ID\", assigneeIds:[$IDS_LIST]}) { issue { number } } }"
fi

# Target date
if [ "$SET_TARGET" -eq 1 ] && [ -n "${ISSUE_FIELD_ID[Target date]:-}" ]; then
  fid="${ISSUE_FIELD_ID[Target date]}"
  if [ "$TARGET_DATE" = "clear" ]; then
    try "target date = <clear>" "mutation { setIssueFieldValue(input:{issueId:\"$ISSUE_ID\", issueFields:[{fieldId:\"$fid\", delete:true}]}) { issue { number } } }"
  else
    try "target date = $TARGET_DATE" "mutation { setIssueFieldValue(input:{issueId:\"$ISSUE_ID\", issueFields:[{fieldId:\"$fid\", dateValue:\"$TARGET_DATE\"}]}) { issue { number } } }"
  fi
fi

# Start date
if [ "$SET_START" -eq 1 ] && [ -n "${ISSUE_FIELD_ID[Start date]:-}" ]; then
  fid="${ISSUE_FIELD_ID[Start date]}"
  if [ "$START_DATE" = "clear" ]; then
    try "start date = <clear>" "mutation { setIssueFieldValue(input:{issueId:\"$ISSUE_ID\", issueFields:[{fieldId:\"$fid\", delete:true}]}) { issue { number } } }"
  else
    try "start date = $START_DATE" "mutation { setIssueFieldValue(input:{issueId:\"$ISSUE_ID\", issueFields:[{fieldId:\"$fid\", dateValue:\"$START_DATE\"}]}) { issue { number } } }"
  fi
fi

# Status (via ProjectV2)
if [ "$SET_STATUS" -eq 1 ]; then
  # Get or create project item for this issue
  ITEM_ID="$(gh api graphql -f query="
    query { node(id:\"$ISSUE_ID\") { ... on Issue { projectItems(first:10) { nodes { id project { id } } } } } }" \
    | jq -r --arg p "$PROJECT_ID" '.data.node.projectItems.nodes[] | select(.project.id==$p) | .id' | head -1)"
  if [ -z "$ITEM_ID" ]; then
    ITEM_ID="$(gh api graphql -f query="
      mutation { addProjectV2ItemById(input:{projectId:\"$PROJECT_ID\", contentId:\"$ISSUE_ID\"}) { item { id } } }" \
      | jq -r '.data.addProjectV2ItemById.item.id // ""')"
  fi
  if [ -n "$ITEM_ID" ]; then
    try "status = $STATUS" "mutation { updateProjectV2ItemFieldValue(input:{projectId:\"$PROJECT_ID\", itemId:\"$ITEM_ID\", fieldId:\"$STATUS_FIELD_ID\", value:{singleSelectOptionId:\"$STATUS_OPTION_ID\"}}) { projectV2Item { id } } }"
  else
    echo "  ✗ status: could not add issue to project" >&2
    apply_ok=0
  fi
fi

echo ""
if [ "$apply_ok" -eq 1 ]; then
  echo "✓ #$ISSUE updated"
else
  echo "⚠ #$ISSUE partially updated; see errors above" >&2
  exit 1
fi
