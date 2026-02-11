#!/bin/bash
# Initialize pool node data directory for proto-devnet
# Creates genesis with current timestamp, copies pool keys, generates topology, creates leios.db
#
# Usage: init-pool-node.sh [pool-number]
# Example: init-pool-node.sh 1

set -euo pipefail

POOL_NUM="${1:-1}"
POOL_NAME="pool${POOL_NUM}"

echo "=== Initializing ${POOL_NAME} ==="

DATA_DIR="${DATA_DIR:-/data}"
CONFIG_DIR="${CONFIG_DIR:-/app/config}"
GENESIS_DIR="${GENESIS_DIR:-/app/genesis}"
POOLS_KEYS_DIR="${POOLS_KEYS_DIR:-/app/pools-keys}"
SHARED_GENESIS_DIR="${SHARED_GENESIS_DIR:-/shared-genesis}"

# Environment variables for peer addresses (mesh topology)
IP_POOL1="${IP_POOL1:-172.28.0.10}"
IP_POOL2="${IP_POOL2:-172.28.0.20}"
IP_POOL3="${IP_POOL3:-172.28.0.30}"
PORT_POOL1="${PORT_POOL1:-3001}"
PORT_POOL2="${PORT_POOL2:-3002}"
PORT_POOL3="${PORT_POOL3:-3003}"

echo "Configuration:"
echo "  POOL_NAME: $POOL_NAME"
echo "  DATA_DIR: $DATA_DIR"
echo "  SHARED_GENESIS_DIR: $SHARED_GENESIS_DIR"

# Create data directory if needed
mkdir -p "$DATA_DIR"
mkdir -p "$DATA_DIR/genesis"
mkdir -p "$DATA_DIR/keys"

# Handle genesis files - pool1 creates them, others wait and copy
if [ "$POOL_NUM" = "1" ]; then
    echo "Pool1: Creating genesis files with current timestamp..."

    # Get current time for genesis
    startTimeEpoch=$(date +%s)
    startTimeIso=$(date -u -d "@$startTimeEpoch" +"%Y-%m-%dT%H:%M:%SZ")

    echo "  systemStart: $startTimeIso (epoch: $startTimeEpoch)"

    # Update byron-genesis.json with startTime
    jq --argjson time "$startTimeEpoch" '.startTime = $time' \
        "$GENESIS_DIR/byron-genesis.json" > "$DATA_DIR/genesis/byron-genesis.json"

    # Update shelley-genesis.json with systemStart
    jq --arg time "$startTimeIso" '.systemStart = $time' \
        "$GENESIS_DIR/shelley-genesis.json" > "$DATA_DIR/genesis/shelley-genesis.json"

    # Copy remaining genesis files unchanged
    cp "$GENESIS_DIR/alonzo-genesis.json" "$DATA_DIR/genesis/"
    cp "$GENESIS_DIR/conway-genesis.json" "$DATA_DIR/genesis/"
    cp "$GENESIS_DIR/dijkstra-genesis.json" "$DATA_DIR/genesis/"

    # Share genesis files with other pools via shared volume
    mkdir -p "$SHARED_GENESIS_DIR"
    cp "$DATA_DIR/genesis/"*.json "$SHARED_GENESIS_DIR/"

    # Create a marker to signal genesis is ready
    touch "$SHARED_GENESIS_DIR/.genesis-ready"
    echo "  Genesis files created and shared"
else
    echo "Pool${POOL_NUM}: Waiting for pool1 to create genesis files..."

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
    cp "$SHARED_GENESIS_DIR/"*.json "$DATA_DIR/genesis/"
    echo "  Genesis files copied from pool1"
fi

# Copy pool keys
echo "Copying pool keys..."
POOL_KEYS_SRC="$POOLS_KEYS_DIR/$POOL_NAME"
if [ -d "$POOL_KEYS_SRC" ]; then
    cp "$POOL_KEYS_SRC/vrf.skey" "$DATA_DIR/keys/"
    cp "$POOL_KEYS_SRC/kes.skey" "$DATA_DIR/keys/"
    cp "$POOL_KEYS_SRC/opcert.cert" "$DATA_DIR/keys/"
    chmod 400 "$DATA_DIR/keys"/*.skey
    echo "  Keys copied: vrf.skey, kes.skey, opcert.cert"
else
    echo "  WARNING: Pool keys not found at $POOL_KEYS_SRC"
fi

# Generate mesh topology (connect to other pools)
echo "Generating mesh topology..."
accessPoints="["
case "$POOL_NUM" in
    1)
        accessPoints='[{"address": "'$IP_POOL2'", "port": '$PORT_POOL2'}, {"address": "'$IP_POOL3'", "port": '$PORT_POOL3'}]'
        ;;
    2)
        accessPoints='[{"address": "'$IP_POOL1'", "port": '$PORT_POOL1'}, {"address": "'$IP_POOL3'", "port": '$PORT_POOL3'}]'
        ;;
    3)
        accessPoints='[{"address": "'$IP_POOL1'", "port": '$PORT_POOL1'}, {"address": "'$IP_POOL2'", "port": '$PORT_POOL2'}]'
        ;;
esac

jq --argjson accessPoints "$accessPoints" \
    '.localRoots[0].accessPoints = $accessPoints' \
    "$CONFIG_DIR/topology.template.json" > "$DATA_DIR/topology.json"
echo "  topology.json created with mesh topology"

# Copy and customize config
echo "Copying config..."
if [ -f "$CONFIG_DIR/config.json" ]; then
    # Update node name and prometheus port in config
    METRICS_PORT=$((12900 + POOL_NUM))
    cat "$CONFIG_DIR/config.json" | \
        jq ".TraceOptionNodeName = \"$POOL_NAME\"" | \
        jq ".TraceOptions.\"\".backends[1] = \"PrometheusSimple 0.0.0.0 $METRICS_PORT\"" \
        > "$DATA_DIR/config.json"
    echo "  config.json created (metrics port: $METRICS_PORT)"
fi

# Create leios.db from schema if available
echo "Setting up leios.db..."
if [ -f "$CONFIG_DIR/leios-schema.sql" ]; then
    sqlite3 "$DATA_DIR/leios.db" < "$CONFIG_DIR/leios-schema.sql"
    echo "  leios.db created"
else
    echo "  leios-schema.sql not found, skipping leios.db"
fi

echo "=== ${POOL_NAME} initialization complete ==="
