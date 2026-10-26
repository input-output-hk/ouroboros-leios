#!/usr/bin/env bash
# Load a devnet with worst-case Plutus V3 transactions from plutus-network-bench:
# set up its on-chain fixtures and calibrate once, then submit corpus after
# corpus for as long as this runs.
#
# Shared by proto-devnet and dozen-devnet, whose process-compose files run it as
# PlutusBench with:
#
#   SOCKET      the node socket to submit to
#   SKEY        the seed key that pays for it all (utxo-keys/utxo2, funded at
#               genesis for this alone, so it never races the tx-firehoses or a
#               governance action for a UTxO)
#   STATE_ROOT  where the bench keeps its state; under the devnet's working
#               directory, so a fresh devnet starts a fresh bench
#   TPS         worst-case txs per second, each saturating the per-tx budget
#
# The CPU and memory dials need the 350-entry PlutusV3 cost model, which only
# EnactPlutusCostModel puts on chain, so this waits for it.
set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
export CARDANO_NODE_NETWORK_ID=164
export CARDANO_NODE_SOCKET_PATH="$SOCKET"

until [ "$(cardano-cli dijkstra query protocol-parameters | jq '.costModels.PlutusV3 | length')" = 350 ]; do
  echo "waiting for the 350-entry PlutusV3 cost model (EnactPlutusCostModel)"
  sleep 60
done

state=$(find "$STATE_ROOT" -mindepth 1 -maxdepth 1 -type d -name 'devnet-*' 2>/dev/null | sort | tail -n 1)
if [ -z "$state" ]; then
  setup-bench --config "$HERE/config.json" --socket "$SOCKET" --skey "$SKEY" --state-dir "$STATE_ROOT"
  state=$(find "$STATE_ROOT" -mindepth 1 -maxdepth 1 -type d -name 'devnet-*' | sort | tail -n 1)
else
  setup-bench --resume "$state" --socket "$SOCKET" --skey "$SKEY"
fi

[ -f "$state/calibration.json" ] || calibrate --state-dir "$state"

while :; do
  run-bench --state-dir "$state" --set "submit.tps=${TPS}"
done
