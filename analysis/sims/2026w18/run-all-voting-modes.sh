#!/usr/bin/env bash
set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

MODES=(wfa-ls everyone top-stake-fraction)

FAILED_MODES=()
for mode in "${MODES[@]}"; do
  echo "=== Voting mode: $mode ==="
  if ! bash "$SCRIPT_DIR/run-sweep.sh" -m "$mode" "$@"; then
    echo "=== Mode $mode had failures — continuing to next mode ===" >&2
    FAILED_MODES+=("$mode")
  fi
  echo ""
done

if [[ ${#FAILED_MODES[@]} -gt 0 ]]; then
  echo "All modes processed. Modes with failures: ${FAILED_MODES[*]}"
  exit 1
else
  echo "All voting mode runs complete."
fi
