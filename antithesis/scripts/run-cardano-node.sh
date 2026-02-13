#!/bin/bash
# Run cardano-node with proper logging
# Usage: run-cardano-node.sh [node-name]

set -euo pipefail

NODE_NAME="${1:-node0}"
DATA_DIR="${DATA_DIR:-/data}"
LOG_DIR="${LOG_DIR:-/logs}"
PORT="${PORT:-3002}"

echo "=== Starting cardano-node ($NODE_NAME) ==="

# Setup WAN emulation if enabled
if [ "${ENABLE_WAN_EMULATION:-false}" = "true" ]; then
    echo "Setting up WAN emulation..."
    /app/scripts/setup-wan-emulation.sh || echo "WAN emulation setup failed (continuing anyway)"
fi

# Ensure log directory exists
mkdir -p "$LOG_DIR"

# Set LEIOS_DB_PATH for the node
export LEIOS_DB_PATH="$DATA_DIR/leios.db"

echo "Configuration:"
echo "  NODE_NAME: $NODE_NAME"
echo "  DATA_DIR: $DATA_DIR"
echo "  LOG_DIR: $LOG_DIR"
echo "  PORT: $PORT"
echo "  LEIOS_DB_PATH: $LEIOS_DB_PATH"

# Run cardano-node with tee to both stdout and log file
exec cardano-node run \
    --config "$DATA_DIR/config.json" \
    --topology "$DATA_DIR/topology.json" \
    --database-path "$DATA_DIR/db" \
    --socket-path "$DATA_DIR/socket" \
    --host-addr 0.0.0.0 \
    --port "$PORT" \
    2>&1 | tee "$LOG_DIR/${NODE_NAME}.log"
