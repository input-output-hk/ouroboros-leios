#!/usr/bin/env bash
set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

MODES=(wfa-ls everyone top-stake-fraction)

for mode in "${MODES[@]}"; do
  echo "=== Voting mode: $mode ==="
  bash "$SCRIPT_DIR/run-all-NA.sh" -m "$mode" "$@"
  echo ""
done

echo "All voting mode runs complete."
