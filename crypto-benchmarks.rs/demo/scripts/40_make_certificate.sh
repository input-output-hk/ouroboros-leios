#!/usr/bin/env bash
set -euo pipefail
# Usage: demo/scripts/40_make_certificate.sh -d RUN_DIR
# Example (from demo/): scripts/40_make_certificate.sh -d run16
# Requires: demo/scripts/.env_cli (set via 00_set_cli.sh)

DIR_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$DIR_SCRIPT/.env_cli"

RUN_DIR=""

# ---- arg parsing ----
while [[ $# -gt 0 ]]; do
  case "$1" in
    -d) RUN_DIR="$2"; shift 2;;
    *) echo "Usage: $0 -d RUN_DIR"; exit 2;;
  esac
done

if [[ -z "$RUN_DIR" ]]; then
  echo "Error: need -d RUN_DIR" >&2
  exit 2
fi

# Resolve run directory relative to demo/
RUN_DIR="$(cd "$DIR_SCRIPT/.."; cd "$RUN_DIR" && pwd)"
echo "== [40_make_certificate] DIR=${RUN_DIR} =="

# ---- preflight ----
if [[ ! -f "${RUN_DIR}/registry.cbor" ]]; then
  echo "Error: ${RUN_DIR}/registry.cbor not found. Run scripts/20_make_registry.sh first." >&2
  exit 1
fi
if [[ ! -f "${RUN_DIR}/votes.cbor" ]]; then
  echo "Error: ${RUN_DIR}/votes.cbor not found. Run scripts/30_cast_votes.sh first." >&2
  exit 1
fi

# ---- make certificate ----
pushd "$RUN_DIR" >/dev/null
"$CLI" make-certificate \
  --registry-file registry.cbor \
  --votes-file votes.cbor \
  --certificate-file certificate.cbor
popd >/dev/null


# ---- summary output ----
echo
echo "== Certificate creation summary =="
BYTES_CERT="$(wc -c < "${RUN_DIR}/certificate.cbor" 2>/dev/null || echo "?")"
echo "Certificate size (bytes): ${BYTES_CERT}"
