

#!/usr/bin/env bash
set -euo pipefail
# Orchestrate a full demo run end-to-end in one go.
#
# Usage:
#   scripts/70_run_one.sh -d RUN_DIR -n N -f FRACTION [-p POOLS] [-t TOTAL_STAKE]
# Examples (from demo/):
#   scripts/70_run_one.sh -d run16 -n 16 -f 1.0
#   scripts/70_run_one.sh -d run32 -n 32 -f 0.85 -p 400 -t 200000
#
# Notes:
# - This is a convenience wrapper that calls:
#     10_init_inputs.sh
#     20_make_registry.sh
#     30_cast_votes.sh
#     40_make_certificate.sh
#     50_verify_certificate.sh
#     60_pretty_print_cert.sh
# - Each sub-script prints its own status; this wrapper adds a compact summary.

DIR_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEMO_ROOT="$(cd "$DIR_SCRIPT/.." && pwd)"

RUN_DIR=""
N=""
FRACTION=""
POOLS=""
TOTAL_STAKE=""

usage() {
  cat <<USAGE
Usage: $0 -d RUN_DIR -n N -f FRACTION [-p POOLS] [-t TOTAL_STAKE]
  -d RUN_DIR       Name of run directory under demo/ (e.g., run16)
  -n N             Voter count (seats)
  -f FRACTION      Participation fraction for cast-votes (e.g., 1.0, 0.85)
  -p POOLS         (optional) Number of pools to generate (default: script's default)
  -t TOTAL_STAKE   (optional) Total stake to allocate (default: script's default)
USAGE
}

# ---- arg parsing ----
while [[ $# -gt 0 ]]; do
  case "$1" in
    -d) RUN_DIR="$2"; shift 2;;
    -n) N="$2"; shift 2;;
    -f) FRACTION="$2"; shift 2;;
    -p) POOLS="$2"; shift 2;;
    -t) TOTAL_STAKE="$2"; shift 2;;
    -h|--help) usage; exit 0;;
    *) echo "Unknown argument: $1" >&2; usage; exit 2;;
  esac
done

if [[ -z "$RUN_DIR" || -z "$N" || -z "$FRACTION" ]]; then
  echo "Error: need -d RUN_DIR, -n N, and -f FRACTION" >&2
  usage; exit 2
fi

RUN_DIR_ABS="$(cd "$DEMO_ROOT"; mkdir -p "$RUN_DIR"; cd "$RUN_DIR" && pwd)"
echo "== [70_run_one] DIR=${RUN_DIR_ABS} N=${N} FRACTION=${FRACTION} POOLS=${POOLS:-default} TOTAL_STAKE=${TOTAL_STAKE:-default} =="

# ---- 10: init inputs ----
INIT_CMD=("$DIR_SCRIPT/10_init_inputs.sh" -d "$RUN_DIR")
[[ -n "$POOLS" ]] && INIT_CMD+=( -p "$POOLS" )
[[ -n "$TOTAL_STAKE" ]] && INIT_CMD+=( -t "$TOTAL_STAKE" )
"${INIT_CMD[@]}"

# ---- 20: make registry ----
"$DIR_SCRIPT/20_make_registry.sh" -d "$RUN_DIR" -n "$N"

# ---- 30: cast votes ----
"$DIR_SCRIPT/30_cast_votes.sh" -d "$RUN_DIR" -f "$FRACTION"

# ---- 40: make certificate ----
"$DIR_SCRIPT/40_make_certificate.sh" -d "$RUN_DIR"

# ---- 50: cryptographic verification ----
"$DIR_SCRIPT/50_verify_certificate.sh" -d "$RUN_DIR"

# ---- 60: show sizes + summary JSON ----
"$DIR_SCRIPT/60_pretty_print_cert.sh" -d "$RUN_DIR"

# ---- 25: generate JSON for UI ----
"$DIR_SCRIPT/25_export_demo_json.sh" -d "$RUN_DIR"

# ---- compact tail summary ----
PRETTY_JSON="${RUN_DIR_ABS}/certificate.pretty.json"
if [[ -f "$PRETTY_JSON" ]] && command -v jq >/dev/null 2>&1; then
  echo "-- Summary --"
  jq '{eid, eb, persistent_voters_count, nonpersistent_voters_count, votes_bytes, certificate_bytes, compression_ratio}' "$PRETTY_JSON"
else
  echo "(Tip) Install jq for a compact summary: brew install jq"
fi

echo "Done."