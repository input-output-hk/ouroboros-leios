#!/usr/bin/env bash
set -euo pipefail

# Generic node run script
# Expects NODE_DIR, IP, and PORT to be set

cd "$NODE_DIR"

export LEIOS_DB_PATH="leios.db"

# A socket left behind by a previous run -- which RESUME=1 guarantees -- satisfies
# the wait below instantly. The waiter then chmods that doomed inode, the node
# unlinks it on startup and binds its own at the node's 0755, and nothing ever
# makes the real one writable. Connecting to a unix socket needs write
# permission, so every non-root client then fails with EACCES. Remove it first,
# so the waiter can only ever see the socket the node actually created.
rm -f "node.socket"

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
  "${FORGE_ARGS[@]}" \
  "${RTS_ARGS[@]}"
