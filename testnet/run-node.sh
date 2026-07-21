#!/usr/bin/env bash
#
# Just-the-node: launch a single Leios-prototype cardano-node as a
# non-block-producing relay against the public Leios testnet
# (leios-node.play.dev.cardano.org). Use directly when you only want
# the node; ./run.sh wraps this under process-compose with X-ray
# observability and a tip-watcher.
#
# Configs in ./config are a pinned snapshot of
#   cardano-playground/docs/environments-pre/leios
# Use ./pin-config.sh to refresh when the upstream testnet rolls.

set -euo pipefail

: "${WORKING_DIR:=$(pwd)/tmp-testnet}"
# Normalize to absolute so subprocesses with different cwds resolve to the
# same path (see testnet/run.sh).
WORKING_DIR="$(realpath -m "$WORKING_DIR")"
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
# Only chmod the top-level files we just copied (nix-store reads come out r-r).
# Avoid descending into db/, loki/, prometheus/, grafana/, ... — those are
# managed live by their own processes and racing with rotation produces
# "No such file or directory" spam.
find "$WORKING_DIR" -mindepth 1 -maxdepth 1 -type f -exec chmod u+w {} +
# Optional topology override — the acceptance harness uses this to point
# nodeA at the zw3rkpool relays and nodeB only at nodeA. Falls through to
# the pinned config/topology.json when unset.
if [ -n "${TOPOLOGY_SRC:-}" ]; then
  cp -f "$TOPOLOGY_SRC" "$WORKING_DIR/topology.json"
fi
cd "$WORKING_DIR"

mkdir -p db

mkdir -p "$(dirname "$LOG_FILE")"

echo "Starting Leios testnet relay"
echo "  binary:    $($CARDANO_NODE --version 2>&1 | head -1)"
echo "  workdir:   $WORKING_DIR"
echo "  bind:      $HOST_ADDR:$PORT"
echo "  topology:  $(jq -c '.bootstrapPeers' topology.json)"
echo "  log file:  $LOG_FILE"

# Append so each restart accumulates on top of the previous run's
# output — otherwise process-compose's restart silently truncates the
# log and we lose forensics on whatever caused the restart. Prefix a
# marker line so it's easy to find run boundaries.
{
  echo "==== run started at $(date -u +%Y-%m-%dT%H:%M:%SZ) (pid $$) ===="
  "$CARDANO_NODE" run \
    --config config.json \
    --host-addr "$HOST_ADDR" \
    --port "$PORT" \
    --topology topology.json \
    --database-path db \
    --socket-path node.socket \
    2>&1
} | tee -a "$LOG_FILE"
