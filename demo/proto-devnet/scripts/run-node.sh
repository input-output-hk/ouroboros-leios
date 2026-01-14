#!/usr/bin/env bash
set -euo pipefail

# Generic node run script that uses NODE_ID environment variable
# Expects WORKING_DIR, CARDANO_NODE, and NODE_ID to be set

NODE_DIR="$WORKING_DIR/node${NODE_ID}"

cd "$NODE_DIR"

# Set LEIOS_DB_PATH environment variable for the node
export LEIOS_DB_PATH="leios.db"

# Run cardano-node
$CARDANO_NODE run \
	--config "config.json" \
	--topology "topology.json" \
	--database-path "db" \
	--socket-path "node.socket" \
	--shelley-vrf-key "keys/vrf.skey" \
	--shelley-kes-key "keys/kes.skey" \
	--shelley-operational-certificate "keys/opcert.cert"
