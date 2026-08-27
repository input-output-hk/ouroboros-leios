#!/usr/bin/env bash
#
# Simple wrapper script to set defaults and check for requirements and runs the
# proto-devnet demo using process-compose
set -eo pipefail

# Set defaults for all environment variables
# These can be overridden by exporting them before running this script
set -a
: "${WORKING_DIR:=$(pwd)/tmp-devnet}"
: "${SOURCE_DIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
# Bootstrap from an archived working dir of a previous run instead of
# starting from genesis
: "${BOOTSTRAP_FROM:=}"
: "${PORT_NODE1:=3001}"
: "${PORT_NODE2:=3002}"
: "${PORT_NODE3:=3003}"
: "${METRICS_PORT_NODE1:=12901}"
: "${METRICS_PORT_NODE2:=12902}"
: "${METRICS_PORT_NODE3:=12903}"
# Base firehose submission rate (TxFirehose1); override with e.g. TPS=1000
: "${TPS:=100}"
# Traffic control (on by default, disable with TC=0)
: "${TC:=1}"
if [ "$TC" = "1" ]; then
  : "${RATE:=50Mbps}"
  : "${DELAY:=100ms}"
  : "${IP_HOST:=172.28.0.1}"
  : "${IP_NODE1:=172.28.0.10}"
  : "${IP_NODE2:=172.28.0.20}"
  : "${IP_NODE3:=172.28.0.30}"
else
  # Use distinct loopback aliases so each node's --host-addr (which
  # ouroboros-network also uses as the source IP for outbound sockets) does
  # not collide with another node's listening 4-tuple. With all three nodes
  # sharing 127.0.0.1, outbound connect() can return EADDRNOTAVAIL because
  # the kernel cannot assign (127.0.0.1:listener_port, 127.0.0.1:peer_port)
  # for the new socket while the listener still owns that port. Splitting
  # across the 127/8 range avoids the collision entirely.
  : "${IP_NODE1:=127.2.0.1}"
  : "${IP_NODE2:=127.2.0.2}"
  : "${IP_NODE3:=127.2.0.3}"
fi
# X-ray observability (on by default, disable with XRAY=0)
: "${XRAY:=1}"
: "${XRAY_SOURCE_DIR:="${SOURCE_DIR}/../extras/x-ray"}"
# Network topology: "mesh" (default, all-to-all) or "line" (Node1-Node2-Node3
# with no direct Node1<->Node3 edge, so Node2 is the only path between the
# ends). Opt in with TOPOLOGY=line.
: "${TOPOLOGY:=mesh}"
set +a

# Check for required commands
REQUIRED_COMMANDS=(
  "process-compose"
  "sqlite3"
  "jq"
  "yq"
  "envsubst"
  "cardano-node"
  "cardano-cli"
  "tx-firehose"
)
if [ "$TC" = "1" ]; then
  REQUIRED_COMMANDS+=("ip" "tc")
fi

MISSING_COMMANDS=()
for cmd in "${REQUIRED_COMMANDS[@]}"; do
  if ! command -v "$cmd" &>/dev/null; then
    MISSING_COMMANDS+=("$cmd")
  fi
done

if [ ${#MISSING_COMMANDS[@]} -gt 0 ]; then
  echo "Error: The following required commands are not available:"
  for cmd in "${MISSING_COMMANDS[@]}"; do
    echo "  - $cmd"
  done
  echo ""
  echo "Please install the missing commands or use nix:"
  echo "  nix run github:input-output-hk/ouroboros-leios#demo-proto-devnet"
  exit 1
fi

# Check if WORKING_DIR already exists
if [ -d "$WORKING_DIR" ]; then
  echo "Working directory already exists: $WORKING_DIR"
  read -r -rp "Remove and re-initialize? (Y/n): " response
  if [[ "$response" =~ ^[Yy]$ || -z "$response" ]]; then
    chmod a+w -R "$WORKING_DIR"
    rm -rf "$WORKING_DIR"
  else
    echo "Aborting."
    exit 0
  fi
fi
echo "Initializing proto-devnet in $WORKING_DIR"

# Create working directory
mkdir -p "$WORKING_DIR"

CONFIG_DIR="${SOURCE_DIR}/config"

# Resolve iproute2 for the elevated processes. sudo drops the environment, so a
# PATH-only iproute2 — the usual case when it comes from a devshell rather than
# the system profile — would leave the namespace scripts unable to find ip.
TOOL_PATH=""
IP_BIN=""
if [ "$TC" = "1" ]; then
  IP_BIN=$(command -v ip)
  TOOL_PATH=$(dirname "$IP_BIN")
  tc_dir=$(dirname "$(command -v tc)")
  if [ "$tc_dir" != "$TOOL_PATH" ]; then
    TOOL_PATH="${TOOL_PATH}:${tc_dir}"
  fi
fi
export TOOL_PATH IP_BIN

nodes=(1 2 3)
if [ -n "$BOOTSTRAP_FROM" ]; then
  # Restore from an archived working dir: reuse its genesis and chain state,
  # but shift the genesis start time forward by the downtime so the archived
  # tip slot maps to ~now and the nodes resume fully caught up (the chain db,
  # leios.db and KES are all slot-based, so shifting wall-clock anchors is
  # safe).
  BOOTSTRAP_DIR="$(cd "$BOOTSTRAP_FROM" && pwd)"
  if [ ! -d "$BOOTSTRAP_DIR/genesis" ]; then
    echo "Error: $BOOTSTRAP_DIR is not an archived working dir (need genesis/)"
    exit 1
  fi
  for i in "${nodes[@]}"; do
    if [ ! -d "$BOOTSTRAP_DIR/node$i/db" ]; then
      echo "Error: $BOOTSTRAP_DIR is missing node$i/db"
      exit 1
    fi
  done

  # Wall time the source run was stopped. The newest file mtime under the
  # nodes' db dirs is an upper bound on the wall time of the last block
  # (chain db files are written as blocks arrive and mtimes are preserved
  # when archiving with cp -a), so anchoring the shift on it guarantees the
  # shifted tip slot ends up in the past — otherwise the nodes would reject
  # their own chain as from-the-future. sqlite sidecar files are excluded:
  # merely reading leios.db can (re)create them, which would inflate the
  # anchor and leave a huge gap of empty slots.
  harvestEpoch=$(find "$BOOTSTRAP_DIR"/node*/db -type f \
    ! -name 'leios.db-wal' ! -name 'leios.db-shm' ! -name 'lock' \
    -printf '%T@\n' | sort -n | tail -1 | cut -d. -f1)

  nowEpoch=$(date +%s)
  shiftDelta=$((nowEpoch - harvestEpoch))
  oldByronStart=$(jq .startTime "$BOOTSTRAP_DIR/genesis/byron-genesis.json")
  newByronStart=$((oldByronStart + shiftDelta))

  # Only byron-genesis.json is rewritten: the consensus wall clock
  # (SystemStart) is anchored on its startTime, and the byron era contains no
  # blocks so its hash is unconstrained. The shelley genesis MUST stay
  # byte-identical — its file hash seeds the initial Praos nonce, and any
  # change invalidates the VRF proofs of every archived block
  # (VRFKeyBadProof at the first volatile block).
  cp -r "$BOOTSTRAP_DIR/genesis" "$WORKING_DIR/genesis"
  chmod u+w -R "${WORKING_DIR}/genesis"

  jq --argjson time "$newByronStart" '.startTime = $time' \
    "$BOOTSTRAP_DIR/genesis/byron-genesis.json" >"$WORKING_DIR/genesis/byron-genesis.json"

  echo "Bootstrapping from archived run: $BOOTSTRAP_DIR"
  echo "  Downtime shift: ${shiftDelta}s, new byron startTime: $(date -u -d "@$newByronStart" +"%Y-%m-%dT%H:%M:%SZ")"
else
  # Copy genesis files and set start time
  cp -r "$CONFIG_DIR/genesis" "$WORKING_DIR/genesis"
  chmod u+w -R "${WORKING_DIR}/genesis"

  startTimeEpoch=$(date +%s)
  startTimeIso=$(date -u -d "@$startTimeEpoch" +"%Y-%m-%dT%H:%M:%SZ")

  jq --argjson time "$startTimeEpoch" '.startTime = $time' \
    "$CONFIG_DIR/genesis/byron-genesis.json" >"$WORKING_DIR/genesis/byron-genesis.json"

  jq --arg time "$startTimeIso" '.systemStart = $time' \
    "$CONFIG_DIR/genesis/shelley-genesis.json" >"$WORKING_DIR/genesis/shelley-genesis.json"
fi

# Set up each node
for i in "${nodes[@]}"; do
  NODE_NAME="node$i"
  NODE_DIR="$WORKING_DIR/$NODE_NAME"
  POOL_DIR="$CONFIG_DIR/pools-keys/pool$i"

  echo "Setting up $NODE_NAME in $NODE_DIR"
  mkdir -p "$NODE_DIR"

  # Copy config files
  cat "$CONFIG_DIR/config.yaml" |
    yq ".TraceOptionNodeName = \"$NODE_NAME\"" |
    yq ".TraceOptions.\"\".backends[1] = \"PrometheusSimple 0.0.0.0 $((12900 + "$i"))\"" \
      >"$NODE_DIR/config.yaml"

  # Generate upstream endpoints. "mesh": every other node. "line": only
  # adjacent nodes (|i-j| == 1), i.e. Node1-Node2-Node3 with no Node1<->Node3.
  # These localRoots are the whole enforcement: config.yaml sets
  # PeerSharing: false with no public/ledger peers, so a node only ever
  # connects to the peers listed here (re-enabling PeerSharing would let the
  # line collapse back toward a mesh).
  accessPoints=$(for j in "${nodes[@]}"; do
    absdiff=$((i - j))
    absdiff=${absdiff#-}
    if { [ "$TOPOLOGY" = "line" ] && [ "$absdiff" -eq 1 ]; } ||
      { [ "$TOPOLOGY" != "line" ] && [ "$i" -ne "$j" ]; }; then
      port="PORT_NODE$j"
      address="IP_NODE$j"
      echo "{ \"port\": ${!port}, \"address\": \"${!address}\" }"
    fi
  done | jq -s '.')
  jq \
    --argjson accessPoints "$accessPoints" \
    '.localRoots[0].accessPoints = $accessPoints' \
    "$CONFIG_DIR/topology.template.json" >"$NODE_DIR/topology.json"

  # Symlink genesis files (shared, read-only)
  ln -s "../genesis/byron-genesis.json" "$NODE_DIR/"
  ln -s "../genesis/shelley-genesis.json" "$NODE_DIR/"
  ln -s "../genesis/alonzo-genesis.json" "$NODE_DIR/"
  ln -s "../genesis/conway-genesis.json" "$NODE_DIR/"
  ln -s "../genesis/dijkstra-genesis.json" "$NODE_DIR/"

  if [ -n "$BOOTSTRAP_FROM" ]; then
    # Restore the chain db (incl. leios.db) from the archived run. A stale
    # db/lock file is harmless (the lock is advisory flock, not the file's
    # existence), and sqlite recovers a leftover leios.db WAL on first open.
    echo "Restoring chain db from $BOOTSTRAP_DIR/$NODE_NAME/db (this can take a while for multi-GB dbs)"
    cp -a "$BOOTSTRAP_DIR/$NODE_NAME/db" "$NODE_DIR/db"
    chmod -R u+w "$NODE_DIR/db"
  fi

  # Copy pool keys and set permissions; an archived run carries the keys its
  # chain was forged with, so take those when bootstrapping
  if [ -n "$BOOTSTRAP_FROM" ]; then
    cp -r "$BOOTSTRAP_DIR/$NODE_NAME/keys" "$NODE_DIR/keys"
    chmod u+w -R "$NODE_DIR/keys"
  else
    cp -r "$POOL_DIR" "$NODE_DIR/keys"
  fi
  chmod 400 "$NODE_DIR/keys"/*.skey
done

# tx-firehose reads its delegator payment/staking .skey files directly from
# $SOURCE_DIR/config/stake-delegators/delegator1/ (see process-compose.yaml).
# No copy or config-file generation needed.

# Configure alloy for x-ray observability (named config.alloy to avoid conflict with alloy/ storage dir)
export ALLOY_CONFIG="${WORKING_DIR}/config.alloy"
envsubst <"${CONFIG_DIR}/alloy.template" >"${ALLOY_CONFIG}"

# Shared per-service Alloy enrichment modules that config.alloy imports via
# import.file. They carry no envsubst vars, so a plain copy suffices.
mkdir -p "${WORKING_DIR}/alloy-modules"
cp "${CONFIG_DIR}/alloy-modules/"*.alloy "${WORKING_DIR}/alloy-modules/"

echo "Starting proto-devnet ..."
echo "  Topology: ${TOPOLOGY}"
# Traffic control integration
TC_COMPOSE=()
if [ "$TC" = "1" ]; then
  TC_COMPOSE=(-f "${SOURCE_DIR}/process-compose-tc.yaml")
  echo "  Traffic control: enabled TC=${TC} (RATE=${RATE}, DELAY=${DELAY})"
else
  echo "  Traffic control: disabled TC=${TC} (nodes on loopback)"
fi
# X-ray observability integration
XRAY_COMPOSE=()
if [ "$XRAY" = "1" ]; then
  set -a
  # shellcheck disable=SC2034
  DEMO_DASHBOARDS_DIR="${SOURCE_DIR}/config/dashboards"
  # shellcheck source=/dev/null
  source "${XRAY_SOURCE_DIR}/env.sh"
  set +a
  XRAY_COMPOSE=(-f "${XRAY_SOURCE_DIR}/process-compose.yaml")
  echo "  X-ray observability: enabled XRAY=${XRAY} (Grafana at http://localhost:3000)"
else
  echo "  X-ray observability: disabled XRAY=${XRAY}"
fi
process-compose --no-server \
  -f "${SOURCE_DIR}/process-compose.yaml" \
  "${TC_COMPOSE[@]}" \
  "${XRAY_COMPOSE[@]}"
