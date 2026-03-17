#!/usr/bin/env bash
# Initialize dingo node data directory for proto-devnet
# Creates genesis with current timestamp, generates topology
#
# Usage: init-dingo-node.sh [dingo-number]
# Example: init-dingo-node.sh 1

set -euo pipefail

DINGO_NUM="${1:-1}"
DINGO_NAME="dingo${DINGO_NUM}"

echo "=== Initializing ${DINGO_NAME} ==="

DATA_DIR="${DATA_DIR:-/data}"
CONFIG_DIR="${CONFIG_DIR:-/app/config}"
GENESIS_DIR="${GENESIS_DIR:-/app/genesis}"
SHARED_GENESIS_DIR="${SHARED_GENESIS_DIR:-/shared-genesis}"

# Environment variables for peer addresses (mesh topology)
IP_POOL1="${IP_POOL1:-172.28.0.10}"
IP_POOL2="${IP_POOL2:-172.28.0.20}"
IP_POOL3="${IP_POOL3:-172.28.0.30}"
IP_DINGO1="${IP_DINGO1:-172.28.0.40}"
PORT_POOL1="${PORT_POOL1:-3001}"
PORT_POOL2="${PORT_POOL2:-3002}"
PORT_POOL3="${PORT_POOL3:-3003}"

echo "Configuration:"
echo "  DINGO_NAME: $DINGO_NAME"
echo "  DATA_DIR: $DATA_DIR"
echo "  SHARED_GENESIS_DIR: $SHARED_GENESIS_DIR"

# Create data directory if needed
mkdir -p "$DATA_DIR"
mkdir -p "$DATA_DIR/keys"

echo "${DINGO_NAME}: Waiting for pool1 to create genesis files..."

# Wait for genesis files to be ready
for i in $(seq 1 60); do
	if [ -f "$SHARED_GENESIS_DIR/.genesis-ready" ]; then
		break
	fi
	echo "  Waiting for genesis... ($i/60)"
	sleep 1
done

if [ ! -f "$SHARED_GENESIS_DIR/.genesis-ready" ]; then
	echo "ERROR: Timeout waiting for genesis files"
	exit 1
fi

# Copy genesis files from shared volume
cp "$SHARED_GENESIS_DIR/"*-genesis.json "$DATA_DIR/"
echo "  Genesis files copied from pool1"

# Generate mesh topology (connect to other nodes)
echo "Generating mesh topology..."
accessPoints='[{"address": "'$IP_POOL1'", "port": '$PORT_POOL1'}, {"address": "'$IP_POOL2'", "port": '$PORT_POOL2'}, {"address": "'$IP_POOL3'", "port": '$PORT_POOL3'}]'
jq --argjson accessPoints "$accessPoints" \
	'.localRoots[0].accessPoints = $accessPoints' \
	"$CONFIG_DIR/topology.template.json" >"$DATA_DIR/topology.json"
echo "  topology.json created with mesh topology"

# Copy and customize config
echo "Copying config..."
if [ -f "$CONFIG_DIR/config.yaml" ]; then
	cp "$CONFIG_DIR/config.yaml" "$DATA_DIR/config.yaml"
	echo "  config.yaml copied"
fi

echo "=== ${DINGO_NAME} initialization complete ==="
