#!/usr/bin/env bash
set -euo pipefail

# Generic node run script
# Expects NODE_DIR, IP, and PORT to be set

cd "$NODE_DIR"

export LEIOS_DB_PATH="leios.db"

# Run cardano-node
cardano-node run \
  --config "config.yaml" \
  --host-addr "$IP" \
  --port "$PORT" \
  --topology "topology.json" \
  --database-path "db" \
  --socket-path "node.socket" \
  --shelley-vrf-key "keys/vrf.skey" \
  --shelley-kes-key "keys/kes.skey" \
  --shelley-operational-certificate "keys/opcert.cert"
