#!/bin/bash
# Initialize upstream (immdb-server) data directory
# Generates leios.db and schedule.json using leiosdemo202510

set -euo pipefail

echo "=== Initializing upstream (immdb-server) ==="

DATA_DIR="${DATA_DIR:-/data}"
CONFIG_DIR="${CONFIG_DIR:-/app/config}"
GENESIS_DIR="${GENESIS_DIR:-/app/genesis}"

# Environment variables with defaults
REF_SLOT="${REF_SLOT:-11}"

echo "Configuration:"
echo "  DATA_DIR: $DATA_DIR"
echo "  REF_SLOT: $REF_SLOT"

# Create data directory if needed
mkdir -p "$DATA_DIR"

# Generate leios.db and base schedule using leiosdemo202510
echo "Generating leios.db and schedule..."
if [ -f "$CONFIG_DIR/manifest.json" ] && command -v leiosdemo202510 &> /dev/null; then
    # Clean up any existing database (leiosdemo202510 requires path to not exist)
    rm -f "$DATA_DIR/leios.db"

    leiosdemo202510 generate \
        "$DATA_DIR/leios.db" \
        "$CONFIG_DIR/manifest.json" \
        "$DATA_DIR/base-schedule.json"
    echo "  leios.db and base-schedule.json created"

    # Adjust schedule timing (default release time)
    RELEASE_TIME="${LEIOS_RELEASE_TIME:-128.9}"
    jq "map(.[0] = $RELEASE_TIME)" "$DATA_DIR/base-schedule.json" > "$DATA_DIR/schedule.json"
    echo "  schedule.json created with release time $RELEASE_TIME"
else
    echo "  WARNING: leiosdemo202510 or manifest.json not found"
    echo "  Creating empty schedule..."
    echo "[]" > "$DATA_DIR/schedule.json"
fi

# Extract immutable chain data
echo "Extracting immutable chain data..."
if [ -f "$CONFIG_DIR/immutable.tar.gz" ]; then
    mkdir -p "$DATA_DIR/immutable"
    tar -xzf "$CONFIG_DIR/immutable.tar.gz" -C "$DATA_DIR/"
    echo "  Immutable data extracted"
else
    echo "  WARNING: immutable.tar.gz not found"
    mkdir -p "$DATA_DIR/immutable"
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
if [ -f "$CONFIG_DIR/upstream-config.json" ]; then
    # Copy and update genesis paths to point to $DATA_DIR/genesis
    sed 's|"../genesis/|"genesis/|g' "$CONFIG_DIR/upstream-config.json" > "$DATA_DIR/config.json"
    echo "  config.json copied with updated genesis paths"
fi

echo "=== upstream initialization complete ==="
