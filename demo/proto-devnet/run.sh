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
: "${PORT_NODE1:=3001}"
: "${PORT_NODE2:=3002}"
: "${PORT_NODE3:=3003}"
: "${METRICS_PORT_NODE1:=12901}"
: "${METRICS_PORT_NODE2:=12902}"
: "${METRICS_PORT_NODE3:=12903}"
# Traffic control (on by default, disable with TC=0)
: "${TC:=1}"
if [ "$TC" = "1" ]; then
	: "${RATE:=10Mbps}"
	: "${DELAY:=200ms}"
	: "${IP_HOST:=172.28.0.1}"
	: "${IP_NODE1:=172.28.0.10}"
	: "${IP_NODE2:=172.28.0.20}"
	: "${IP_NODE3:=172.28.0.30}"
else
	IP_NODE1=127.0.0.1
	IP_NODE2=127.0.0.1
	IP_NODE3=127.0.0.1
fi
# X-ray observability (on by default, disable with XRAY=0)
: "${XRAY:=1}"
: "${XRAY_SOURCE_DIR:="${SOURCE_DIR}/../extras/x-ray"}"
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
	"tx-generator"
)

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

# Copy genesis files and set start time
cp -r "$CONFIG_DIR/genesis" "$WORKING_DIR/genesis"
chmod u+w -R "${WORKING_DIR}/genesis"

startTimeEpoch=$(date +%s)
startTimeIso=$(date -u -d "@$startTimeEpoch" +"%Y-%m-%dT%H:%M:%SZ")

jq --argjson time "$startTimeEpoch" '.startTime = $time' \
	"$CONFIG_DIR/genesis/byron-genesis.json" >"$WORKING_DIR/genesis/byron-genesis.json"

jq --arg time "$startTimeIso" '.systemStart = $time' \
	"$CONFIG_DIR/genesis/shelley-genesis.json" >"$WORKING_DIR/genesis/shelley-genesis.json"

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

	# Generate upstream endpoints to other nodes
	accessPoints=$(for j in "${nodes[@]}"; do
		# Except self
		if [ "$i" -ne "$j" ]; then
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

	# Copy pool keys and set permissions
	cp -r "$POOL_DIR" "$NODE_DIR/keys"
	chmod 400 "$NODE_DIR/keys"/*.skey
done

# Copy utxo-keys for tx-generator and set permissions
echo "Setting up utxo-keys for tx-generator"
cp -r "$CONFIG_DIR/utxo-keys" "$WORKING_DIR/utxo-keys"
find "$WORKING_DIR/utxo-keys" -name "*.skey" -exec chmod 400 {} \;

# Set LOG_PATH to absolute path for x-ray observability
# Use realpath to resolve WORKING_DIR to absolute path
export LOG_PATH="${LOG_PATH:-$(realpath "${WORKING_DIR}")/node*/node.log}"

# Configure tx-generator
envsubst <"${CONFIG_DIR}/gen.template.json" >"${WORKING_DIR}/gen.json"

# Configure alloy for x-ray observability (named config.alloy to avoid conflict with alloy/ storage dir)
export ALLOY_CONFIG="${WORKING_DIR}/config.alloy"
envsubst <"${CONFIG_DIR}/alloy.template" >"${ALLOY_CONFIG}"

echo "Starting proto-devnet ..."
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
