#!/usr/bin/env bash
set -euo pipefail

# Generic node run script
# Expects NODE_DIR, IP, and PORT to be set

cd "$NODE_DIR"

export LEIOS_DB_PATH="leios.db"

# Make socket accessible to non-root (node runs elevated for namespace access).
# Killed via the EXIT trap below so it doesn't outlive cardano-node: if the
# node dies before creating node.socket (e.g. a startup crash), this loop
# would otherwise leak as an orphan (reparented to PID 1) polling forever,
# since the socket it's waiting for will never appear.
(
  while [ ! -S "node.socket" ]; do sleep 0.1; done
  chmod a+rw "node.socket"
) &
chmod_helper_pid=$!
trap 'kill "$chmod_helper_pid" 2>/dev/null || true' EXIT

# Run cardano-node. CARDANO_NODE is passed in as an absolute path by run.sh
# (sudo/is_elevated drops PATH, same reason ip/tc are invoked by absolute
# path); fall back to a bare PATH lookup when run without elevation (TC=0).
"${CARDANO_NODE:-cardano-node}" run \
  --config "config.yaml" \
  --host-addr "$IP" \
  --port "$PORT" \
  --topology "topology.json" \
  --database-path "db" \
  --socket-path "node.socket" \
  --shelley-vrf-key "keys/vrf.skey" \
  --shelley-kes-key "keys/kes.skey" \
  --shelley-bls-key "keys/bls.skey" \
  --shelley-operational-certificate "keys/opcert.cert"
