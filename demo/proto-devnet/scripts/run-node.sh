#!/usr/bin/env bash
set -exuo pipefail

# Generic node run script that uses NODE_ID environment variable
# Expects WORKING_DIR, CARDANO_NODE, and NODE_ID to be set

NODE_DIR="$WORKING_DIR/node-data/node${NODE_ID}"

cd "$NODE_DIR"

# Set LEIOS_DB_PATH environment variable for the node
export LEIOS_DB_PATH="leios.db"

# Run cardano-node
$CARDANO_NODE run \
  --config "config.json" \
  --topology "topology.json" \
  --database-path "db" \
  --socket-path "../../../socket/node${NODE_ID}/sock" \
  --shelley-vrf-key "shelley/vrf.skey" \
  --shelley-kes-key "shelley/kes.skey" \
  --shelley-operational-certificate "shelley/opcert.cert"
