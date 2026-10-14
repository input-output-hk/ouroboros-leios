#!/usr/bin/env bash
set -euo pipefail

# Generic node run script
# Expects NODE_DIR, IP, and PORT to be set; NODE_BIN picks the cardano-node.
# A node without keys/ runs as a relay.

cd "$NODE_DIR"

export LEIOS_VOL_DB_PATH="leios.db.vol"
export LEIOS_IMM_DB_PATH="leios.db.imm"

# Make socket accessible to non-root (node runs elevated for namespace access)
(
  while [ ! -S "node.socket" ]; do sleep 0.1; done
  chmod a+rw "node.socket"
) &

KEY_ARGS=()
if [ -d keys ]; then
  KEY_ARGS=(
    --shelley-vrf-key "keys/vrf.skey"
    --shelley-kes-key "keys/kes.skey"
    --shelley-bls-key "keys/bls.skey"
    --shelley-operational-certificate "keys/opcert.cert"
  )
fi

"${NODE_BIN:-cardano-node}" run \
  --config "config.yaml" \
  --host-addr "$IP" \
  --port "$PORT" \
  --topology "topology.json" \
  --database-path "db" \
  --socket-path "node.socket" \
  "${KEY_ARGS[@]}"
