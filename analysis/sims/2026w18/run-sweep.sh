#!/usr/bin/env bash
set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

NA_EXPERIMENTS=(
  NA,0.150
  NA,0.200
  NA,0.250
  NA,0.300
  NA,0.350
)

PLUTUS_EXPERIMENTS=(
  1000,0.250
  2000,0.250
  5000,0.250
  10000,0.250
  20000,0.250
  50000,0.250
)

INCLUDE_NA=true
INCLUDE_PLUTUS=true
PASSTHROUGH=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --na-only)     INCLUDE_PLUTUS=false; shift ;;
    --plutus-only) INCLUDE_NA=false; shift ;;
    *)             PASSTHROUGH+=("$1"); shift ;;
  esac
done

EXPERIMENTS=()
[[ "$INCLUDE_NA" == "true" ]]     && EXPERIMENTS+=("${NA_EXPERIMENTS[@]}")
[[ "$INCLUDE_PLUTUS" == "true" ]] && EXPERIMENTS+=("${PLUTUS_EXPERIMENTS[@]}")

echo "Running ${#EXPERIMENTS[@]} experiments"
echo "Args: ${PASSTHROUGH[*]}"
echo ""

FAILED=()
for exp in "${EXPERIMENTS[@]}"; do
  dir="$SCRIPT_DIR/experiments/$exp"
  if [[ ! -d "$dir" ]]; then
    echo "WARNING: $dir not found, skipping" >&2
    continue
  fi
  echo "=== $exp ==="
  start=$(date +%s)
  if (cd "$dir" && bash "$SCRIPT_DIR/run-deterministic.sh" "${PASSTHROUGH[@]}"); then
    end=$(date +%s)
    echo "=== $exp done in $((end - start))s ==="
  else
    rc=$?
    end=$(date +%s)
    echo "=== $exp FAILED (exit $rc) after $((end - start))s — continuing ===" >&2
    FAILED+=("$exp")
  fi
  echo ""
done

if [[ ${#FAILED[@]} -gt 0 ]]; then
  echo "All experiments processed. ${#FAILED[@]} failed: ${FAILED[*]}"
  exit 1
else
  echo "All experiments complete."
fi
