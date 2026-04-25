#!/usr/bin/env bash
set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

EXPERIMENTS=(
  NA,0.150
  NA,0.200
  NA,0.250
  NA,0.300
  NA,0.350
)

echo "Running ${#EXPERIMENTS[@]} NA experiments"
echo "Args: $*"
echo ""

for exp in "${EXPERIMENTS[@]}"; do
  dir="$SCRIPT_DIR/$exp"
  if [[ ! -d "$dir" ]]; then
    echo "WARNING: $dir not found, skipping" >&2
    continue
  fi
  echo "=== $exp ==="
  start=$(date +%s)
  (cd "$dir" && bash "$SCRIPT_DIR/run-deterministic.sh" "$@")
  end=$(date +%s)
  echo "=== $exp done in $((end - start))s ==="
  echo ""
done

echo "All experiments complete."
