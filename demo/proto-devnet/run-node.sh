#!/usr/bin/env bash
set -euo pipefail

# Generic node run script that uses NODE_ID environment variable
# Expects WORKING_DIR and NODE_ID to be set

NODE_DIR="$WORKING_DIR/node${NODE_ID}"

cd "$NODE_DIR"

# Select ip and port from environment variables using NODE_ID
ip="IP_NODE${NODE_ID}"
port="PORT_NODE${NODE_ID}"

export LEIOS_DB_PATH="leios.db"

# Run cardano-node
cardano-node run \
  --config "config.json" \
  --host-addr "${!ip}" \
  --port "${!port}" \
  --topology "topology.json" \
  --database-path "db" \
  --socket-path "node.socket" \
  --shelley-vrf-key "keys/vrf.skey" \
  --shelley-kes-key "keys/kes.skey" \
  --shelley-operational-certificate "keys/opcert.cert"
