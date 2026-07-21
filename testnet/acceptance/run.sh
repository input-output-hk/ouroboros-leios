#!/usr/bin/env bash
#
# Driver for the ShelleyBlock wire-bytes memo hotfix acceptance test.
# Runs everything under process-compose.
#
# Prerequisite: extract a leios3-rel-c-1 snapshot (chain + LeiosDB) into
# $WORKING_DIR/nodeA/ before running — the harness only prunes; it does
# not download.
#
# Workflow:
#   0. PruneImmutable iteratively deletes the highest-numbered chunk
#      trios from nodeA/db/immutable/ until the contentious block header
#      hash is no longer present.
#   1. NodeA syncs whatever we chopped from
#      leios-node.play.dev.cardano.org:3001 and continues past block
#      67555 to current tip.
#   2. NodeB — bootstrap peer only on 127.0.0.1:3010 — mirrors NodeA.
#   3. AssertSync polls both nodes and exits 0 once NodeB catches up to
#      NodeA at a block past 67555.
#
# Usage:
#   CARDANO_NODE=/path/to/further-fixed/cardano-node ./run.sh
#
# Exit code follows AssertSync.

set -eo pipefail

: "${WORKING_DIR:=$(pwd)/tmp-acceptance}"
WORKING_DIR="$(realpath -m "$WORKING_DIR")"
# Kept distinct from run-node.sh's SOURCE_DIR — see process-compose.yaml.
ACCEPTANCE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${TESTNET_DIR:=$(cd "$ACCEPTANCE_DIR/.." && pwd)}"

: "${CARDANO_NODE:=cardano-node}"

for cmd in process-compose cardano-node cardano-cli jq; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "error: required command not on PATH: $cmd" >&2
    exit 1
  fi
done

export WORKING_DIR ACCEPTANCE_DIR TESTNET_DIR CARDANO_NODE
mkdir -p "$WORKING_DIR"

echo "Running ShelleyBlock hotfix acceptance test"
echo "  binary:      $($CARDANO_NODE --version 2>&1 | head -1)"
echo "  workdir:     $WORKING_DIR"
echo "  Prune:       trim highest immutable chunks until block 67555 is absent"
echo "  NodeA:       leios-node.play.dev.cardano.org:3001 — port 3010"
echo "  NodeB:       127.0.0.1:3010 (NodeA) — port 3011"
echo "  Assertion:   NodeB tip past block 67556, matching NodeA"

process-compose --no-server -f "$ACCEPTANCE_DIR/process-compose.yaml"
