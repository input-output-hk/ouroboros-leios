#!/usr/bin/env bash
#
# Re-pin the local snapshot of the Leios testnet config from
# cardano-playground. Defaults to the next-2026-05-15 branch; pass a
# different ref as the first argument to update.

set -euo pipefail

REF="${1:-next-2026-05-15}"
# Canonical configs live under docs/; the static/ tree is generated for
# the book site and lags behind redeployments.
BASE="https://raw.githubusercontent.com/input-output-hk/cardano-playground/${REF}/docs/environments-pre/leios"
DEST="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/config"

mkdir -p "$DEST"

for f in \
  alonzo-genesis.json \
  byron-genesis.json \
  config.json \
  conway-genesis.json \
  dijkstra-genesis.json \
  peer-snapshot.json \
  shelley-genesis.json \
  topology.json
do
  printf '  %-26s' "$f"
  curl -sfo "$DEST/$f" "$BASE/$f" && printf 'ok (%d bytes)\n' "$(wc -c < "$DEST/$f")"
done

echo "Pinned to cardano-playground@$REF"
