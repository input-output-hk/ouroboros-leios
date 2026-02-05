#!/bin/bash
# Initialize downstream node data directory
# Creates leios.db and topology.json (connecting to node0)

set -euo pipefail

echo "=== Initializing downstream node ==="

DATA_DIR="${DATA_DIR:-/data}"
CONFIG_DIR="${CONFIG_DIR:-/app/config}"
GENESIS_DIR="${GENESIS_DIR:-/app/genesis}"

# Environment variables with defaults
IP_NODE0="${IP_NODE0:-10.0.0.2}"
PORT_NODE0="${PORT_NODE0:-3002}"

echo "Configuration:"
echo "  DATA_DIR: $DATA_DIR"
echo "  Node0: $IP_NODE0:$PORT_NODE0"

# Create data directory if needed
mkdir -p "$DATA_DIR"

# Create leios.db from schema
echo "Creating leios.db from schema..."
if [ -f "$CONFIG_DIR/leios-schema.sql" ]; then
    sqlite3 "$DATA_DIR/leios.db" < "$CONFIG_DIR/leios-schema.sql"
    echo "  leios.db created"
else
    echo "  WARNING: leios-schema.sql not found, skipping"
fi

# Generate topology.json from template (connecting to node0)
echo "Generating topology.json..."
if [ -f "$CONFIG_DIR/topology.template.json" ]; then
    jq \
        --argjson port "$PORT_NODE0" \
        --arg address "$IP_NODE0" \
        '.localRoots[0].accessPoints[0].port = $port | .localRoots[0].accessPoints[0].address = $address' \
        "$CONFIG_DIR/topology.template.json" > "$DATA_DIR/topology.json"
    echo "  topology.json created"
else
    echo "  WARNING: topology.template.json not found"
fi

# Copy genesis files to data volume (so they persist)
echo "Setting up genesis files..."
mkdir -p "$DATA_DIR/genesis"
for f in "$GENESIS_DIR"/*.json; do
    if [ -f "$f" ]; then
        cp "$f" "$DATA_DIR/genesis/$(basename $f)"
    fi
done
echo "  Genesis files copied to $DATA_DIR/genesis"

# Copy config file and update genesis paths
echo "Copying and patching config..."
if [ -f "$CONFIG_DIR/downstream-config.json" ]; then
    # Copy and update genesis paths to point to $DATA_DIR/genesis
    sed 's|"../genesis/|"genesis/|g' "$CONFIG_DIR/downstream-config.json" > "$DATA_DIR/config.json"
    echo "  config.json copied with updated genesis paths"
fi

echo "=== downstream initialization complete ==="
