#!/usr/bin/env bash
#
# Connect a Leios-prototype cardano-node to the public Leios testnet
# (https://book.play.dev.cardano.org/environments-pre/leios) as a
# non-block-producing relay. Use this to verify a locally-built node
# can catch up to the testnet chain via the CertRB staging area
# (issue #890) and the Phase 2 emergency-fetch path.
#
# Configs in ./config are a snapshot of
#   cardano-playground/static/book.play.dev.cardano.org/environments-pre/leios
# at tag/branch next-2026-05-15. Re-pin with ./pin-config.sh when the
# upstream testnet rolls.

set -euo pipefail

: "${WORKING_DIR:=$(pwd)/tmp-testnet}"
: "${SOURCE_DIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
: "${PORT:=3010}"
: "${HOST_ADDR:=0.0.0.0}"
: "${LOG_FILE:=${WORKING_DIR}/node.log}"

# cardano-node binary. Override CARDANO_NODE to point at the locally
# built one with the issue-#890 staging fixes, e.g.
#   CARDANO_NODE=/path/to/cardano-node/dist-newstyle/.../cardano-node ./run.sh
: "${CARDANO_NODE:=cardano-node}"

if ! command -v "$CARDANO_NODE" >/dev/null 2>&1; then
  echo "error: cardano-node not on PATH and CARDANO_NODE not set" >&2
  exit 1
fi

mkdir -p "$WORKING_DIR"
cp -rf "$SOURCE_DIR/config/." "$WORKING_DIR/"
chmod u+w -R "$WORKING_DIR"
cd "$WORKING_DIR"

mkdir -p db

mkdir -p "$(dirname "$LOG_FILE")"

echo "Starting Leios testnet relay"
echo "  binary:    $($CARDANO_NODE --version 2>&1 | head -1)"
echo "  workdir:   $WORKING_DIR"
echo "  bind:      $HOST_ADDR:$PORT"
echo "  topology:  $(jq -c '.bootstrapPeers' topology.json)"
echo "  log file:  $LOG_FILE"

"$CARDANO_NODE" run \
  --config config.json \
  --host-addr "$HOST_ADDR" \
  --port "$PORT" \
  --topology topology.json \
  --database-path db \
  --socket-path node.socket \
  2>&1 | tee "$LOG_FILE"
