#!/usr/bin/env bash
#
# Re-pin the local snapshot of the Leios testnet config from
# book.play.dev.cardano.org (the deployed configuration for the
# `musashi` network). Pass a different base URL as the first argument
# to override, e.g. to pull from a staging site or a raw
# cardano-playground branch.

set -euo pipefail

BASE="${1:-https://book.play.dev.cardano.org/environments-pre/leios}"
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

echo "Pinned from $BASE"
