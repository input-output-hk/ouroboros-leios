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
# Reuse an existing WORKING_DIR instead of wiping it, keeping every node's
# databases so the cluster continues the chain it was on. Genesis is left exactly
# as it was -- moving systemStart would invalidate all persisted data -- while
# configs, topology, compose files and observability are regenerated, so config
# edits still take effect. Best effort: see the preflight warnings below.
: "${RESUME:=0}"
: "${PORT_NODE1:=3001}"
: "${PORT_NODE2:=3002}"
: "${PORT_NODE3:=3003}"
: "${METRICS_PORT_NODE1:=12901}"
: "${METRICS_PORT_NODE2:=12902}"
: "${METRICS_PORT_NODE3:=12903}"
# Base firehose submission rate (TxFirehose1); override with e.g. TPS=1000
: "${TPS:=100}"
# Colours the two generators tag their transactions with, so the mempool
# observers can tell whose load each node is holding. Explicit and well
# separated rather than --color auto, which is uniform but can put two
# generators close enough to be hard to tell apart by eye.
: "${COLOR1:=ff0000}"
: "${COLOR2:=00a0ff}"
# Mempool observers are not devnet processes: process-compose cannot tile. Point
# ../dozen-devnet/mempool-panes.sh at this devnet instead:
#   NODES="node1 node2 node3" WORKING_DIR=... ../dozen-devnet/mempool-panes.sh
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
  if [ "$RESUME" = "1" ]; then
    echo "RESUME=1: keeping $WORKING_DIR"
  else
    # Never destructive from a prompt: a mistyped answer would throw away a
    # run that may have taken hours to reach the state being investigated.
    echo "Working directory already exists: $WORKING_DIR"
    read -r -rp "Resume from persisted data? (Y/n): " response
    if [[ "$response" =~ ^[Yy]$ || -z "$response" ]]; then
      RESUME=1
    else
      echo "Aborting. To start fresh, remove the working directory first:"
      echo "  chmod a+w -R \"$WORKING_DIR\" && rm -rf \"$WORKING_DIR\""
      exit 0
    fi
  fi
elif [ "$RESUME" = "1" ]; then
  echo "RESUME=1 but $WORKING_DIR does not exist; initializing from scratch."
  RESUME=0
fi

if [ "$RESUME" = "1" ]; then
  # Genesis is the anchor: every persisted chain is only valid against the
  # systemStart it was produced under, so this is the one thing a resume must
  # not touch.
  if [ ! -f "$WORKING_DIR/genesis/shelley-genesis.json" ]; then
    echo "Error: RESUME=1 but $WORKING_DIR/genesis is missing -- cannot resume." >&2
    exit 1
  fi
  resume_start=$(jq -r '.systemStart' "$WORKING_DIR/genesis/shelley-genesis.json")
  echo "Resuming proto-devnet in $WORKING_DIR (systemStart $resume_start, preserved)"
  # The Leios database has no schema migration, so a node built after a schema
  # change cannot open one written before it. Cheap detection: the CREATE
  # statements are stored as text in the file.
  for db in "$WORKING_DIR"/*/db/leios.db; do
    [ -e "$db" ] || continue
    if ! grep -qa "ebsMissingTxs" "$db"; then
      echo "Warning: $db predates the ebsMissingTxs schema; this node will" >&2
      echo "         fail to start. Delete the node's db/ to let it resync." >&2
    fi
  done
  # Chain state is far enough along that the firehose's own view of the UTxO may
  # no longer match; if it wedges, that is the first thing to suspect.
  echo "Note: resume is best effort -- tx-firehose state is not checkpointed."
else
  echo "Initializing proto-devnet in $WORKING_DIR"
fi

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

# Copy genesis files and set start time. Skipped on resume: a new systemStart
# would orphan every persisted chain.
if [ "$RESUME" != "1" ]; then
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
nodes=(1 2 3)
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
  ln -sf "../genesis/byron-genesis.json" "$NODE_DIR/"
  ln -sf "../genesis/shelley-genesis.json" "$NODE_DIR/"
  ln -sf "../genesis/alonzo-genesis.json" "$NODE_DIR/"
  ln -sf "../genesis/conway-genesis.json" "$NODE_DIR/"
  ln -sf "../genesis/dijkstra-genesis.json" "$NODE_DIR/"

  # Copy pool keys and set permissions. Not re-copied on resume: 'cp -r' onto
  # an existing keys/ would nest it, and the keys are identical anyway.
  if [ ! -d "$NODE_DIR/keys" ]; then
    cp -r "$POOL_DIR" "$NODE_DIR/keys"
    chmod 400 "$NODE_DIR/keys"/*.skey
  fi
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
echo "  Resume: RESUME=${RESUME}"
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
