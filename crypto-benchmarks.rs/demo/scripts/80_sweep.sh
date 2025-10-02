#!/usr/bin/env bash
set -euo pipefail
# Sweep over multiple voter counts and collect size/gain metrics.
#
# Usage:
#   scripts/80_sweep.sh -d DIR -f FRACTION --ns "16 32 64 128" [-p POOLS] [-t TOTAL_STAKE]
# Examples:
#   scripts/80_sweep.sh -d sweep1 -f 1.0 --ns "16 32 64 128"
#   scripts/80_sweep.sh -d sweepA -f 0.85 --ns "16 32" -p 400 -t 200000
#
# Notes:
# - Creates sub-runs under demo/<DIR>/run<N> and calls scripts/70_run_one.sh for each N
# - Appends results to demo/<DIR>/sweep_results.csv with columns:
#     N,votes_bytes,certificate_bytes,compression_ratio,nonpersistent_voters_count,persistent_voters_count

DIR_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEMO_ROOT="$(cd "$DIR_SCRIPT/.." && pwd)"

BASE_DIR=""
FRACTION=""
NS_LIST=""
POOLS=""
TOTAL_STAKE=""

usage() {
  cat <<USAGE
Usage: $0 -d DIR -f FRACTION --ns "N1 N2 ..." [-p POOLS] [-t TOTAL_STAKE]
  -d DIR          Base directory under demo/ to store runs (e.g., sweep1)
  -f FRACTION     Participation fraction for cast-votes (e.g., 1.0, 0.85)
  --ns "..."      Space-separated list of voter counts (e.g., "16 32 64 128")
  -p POOLS        (optional) Number of pools to generate per run
  -t TOTAL_STAKE  (optional) Total stake to allocate per run
USAGE
}

# ---- arg parsing ----
while [[ $# -gt 0 ]]; do
  case "$1" in
    -d) BASE_DIR="$2"; shift 2;;
    -f) FRACTION="$2"; shift 2;;
    --ns) NS_LIST="$2"; shift 2;;
    -p) POOLS="$2"; shift 2;;
    -t) TOTAL_STAKE="$2"; shift 2;;
    -h|--help) usage; exit 0;;
    *) echo "Unknown argument: $1" >&2; usage; exit 2;;
  esac
done

if [[ -z "$BASE_DIR" || -z "$FRACTION" || -z "$NS_LIST" ]]; then
  echo "Error: need -d DIR, -f FRACTION, and --ns \"N1 N2 ...\"" >&2
  usage; exit 2
fi

BASE_ABS="$(cd "$DEMO_ROOT"; mkdir -p "$BASE_DIR"; cd "$BASE_DIR" && pwd)"
RESULTS_CSV="${BASE_ABS}/sweep_results.csv"

# header
if [[ ! -f "$RESULTS_CSV" ]]; then
  echo "N,votes_bytes,certificate_bytes,compression_ratio,nonpersistent_voters_count,persistent_voters_count" > "$RESULTS_CSV"
fi

echo "== [80_sweep] BASE=${BASE_ABS} FRACTION=${FRACTION} NS=(${NS_LIST}) POOLS=${POOLS:-default} TOTAL_STAKE=${TOTAL_STAKE:-default} =="

for N in ${NS_LIST}; do
  RUN_DIR_REL="${BASE_DIR}/run${N}"
  echo "-- N=${N} -> ${RUN_DIR_REL}"

  # Build command for a single run
  ONE_CMD=("$DIR_SCRIPT/70_run_one.sh" -d "$RUN_DIR_REL" -n "$N" -f "$FRACTION")
  [[ -n "$POOLS" ]] && ONE_CMD+=( -p "$POOLS" )
  [[ -n "$TOTAL_STAKE" ]] && ONE_CMD+=( -t "$TOTAL_STAKE" )

  # Execute
  "${ONE_CMD[@]}"

  PRETTY_JSON="${DEMO_ROOT}/${RUN_DIR_REL}/certificate.pretty.json"
  if [[ -f "$PRETTY_JSON" ]]; then
    # Extract fields with jq; fall back to Python if jq is not available
    if command -v jq >/dev/null 2>&1; then
      VOTES=$(jq -r '.votes_bytes' "$PRETTY_JSON")
      CERT=$(jq -r '.certificate_bytes' "$PRETTY_JSON")
      RATIO=$(jq -r '.compression_ratio' "$PRETTY_JSON")
      NP=$(jq -r '.nonpersistent_voters_count' "$PRETTY_JSON")
      PV=$(jq -r '.persistent_voters_count' "$PRETTY_JSON")
    else
      # Python fallback (no jq). Use a simple one-liner and parse.
      PY_OUT=$(python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d.get("votes_bytes"), d.get("certificate_bytes"), d.get("compression_ratio"), d.get("nonpersistent_voters_count"), d.get("persistent_voters_count"))' "$PRETTY_JSON")
      read -r VOTES CERT RATIO NP PV <<< "$PY_OUT"
    fi
    echo "${N},${VOTES},${CERT},${RATIO},${NP},${PV}" >> "$RESULTS_CSV"
  else
    echo "Warning: ${PRETTY_JSON} not found; skipping CSV append" >&2
  fi

done

echo "Sweep complete. Results: ${RESULTS_CSV}"
