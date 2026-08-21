#!/usr/bin/env bash
set -euo pipefail

# Generic node run script
# Expects NODE_DIR, IP, and PORT to be set

cd "$NODE_DIR"

export LEIOS_DB_PATH="leios.db"

# Make socket accessible to non-root (node runs elevated for namespace access)
(
  while [ ! -S "node.socket" ]; do sleep 0.1; done
  chmod a+rw "node.socket"
) &

# Only block producers have pool keys copied into keys/ by run.sh; a relay runs
# with none of the forging arguments at all.
FORGE_ARGS=()
if [ -f "keys/vrf.skey" ]; then
  FORGE_ARGS=(
    --shelley-vrf-key "keys/vrf.skey"
    --shelley-kes-key "keys/kes.skey"
    --shelley-bls-key "keys/bls.skey"
    --shelley-operational-certificate "keys/opcert.cert"
  )
fi

# Extra RTS options, appended after the ones baked into the binary
# (-T -I0 -A16m -qg1 -qb1 -N2), so a later flag wins. Twelve nodes at the
# built-in -N2 is 24 capabilities, which oversubscribes a 16-core box and
# leaves a 64-thread one two thirds idle — hence the knob.
#   NODE_RTS="-N4"            more parallelism per node on a big host
#   NODE_RTS="-N1"            squeeze more nodes onto a small one
# Empty means whatever the binary was built with.
RTS_ARGS=()
if [ -n "${NODE_RTS:-}" ]; then
  # shellcheck disable=SC2206 # deliberate word splitting: NODE_RTS is a flag list
  RTS_ARGS=(+RTS ${NODE_RTS} -RTS)
fi

# Run cardano-node
cardano-node run \
  --config "config.yaml" \
  --host-addr "$IP" \
  --port "$PORT" \
  --topology "topology.json" \
  --database-path "db" \
  --socket-path "node.socket" \
  "${FORGE_ARGS[@]}" \
  "${RTS_ARGS[@]}"
