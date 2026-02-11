#!/bin/bash
# Run cardano-node as block producer with pool credentials
# Usage: run-pool-node.sh [pool-name]
# Example: run-pool-node.sh pool1

set -euo pipefail

POOL_NAME="${1:-pool1}"
# Extract pool number from name (e.g., "pool1" -> "1")
POOL_NUM="${POOL_NAME#pool}"

DATA_DIR="${DATA_DIR:-/data}"
LOG_DIR="${LOG_DIR:-/logs}"
PORT="${PORT:-3001}"

echo "=== Starting cardano-node ($POOL_NAME) as block producer ==="

# Setup WAN emulation if enabled
if [ "${ENABLE_WAN_EMULATION:-false}" = "true" ]; then
    echo "Setting up WAN emulation..."
    /app/scripts/setup-wan-emulation.sh || echo "WAN emulation setup failed (continuing anyway)"
fi

# Ensure log directory exists
mkdir -p "$LOG_DIR"

# Set LEIOS_DB_PATH for the node
export LEIOS_DB_PATH="$DATA_DIR/leios.db"

# Verify required files exist
for required_file in config.json topology.json shelley-genesis.json keys/vrf.skey keys/kes.skey keys/opcert.cert; do
    if [ ! -f "$DATA_DIR/$required_file" ]; then
        echo "ERROR: Required file not found: $DATA_DIR/$required_file"
        exit 1
    fi
done

echo "Configuration:"
echo "  POOL_NAME: $POOL_NAME"
echo "  DATA_DIR: $DATA_DIR"
echo "  LOG_DIR: $LOG_DIR"
echo "  PORT: $PORT"
echo "  LEIOS_DB_PATH: $LEIOS_DB_PATH"

# Run cardano-node as block producer with pool credentials
exec cardano-node run \
    --config "$DATA_DIR/config.json" \
    --topology "$DATA_DIR/topology.json" \
    --database-path "$DATA_DIR/db" \
    --socket-path "$DATA_DIR/socket" \
    --host-addr 0.0.0.0 \
    --port "$PORT" \
    --shelley-vrf-key "$DATA_DIR/keys/vrf.skey" \
    --shelley-kes-key "$DATA_DIR/keys/kes.skey" \
    --shelley-operational-certificate "$DATA_DIR/keys/opcert.cert" \
    2>&1 | tee "$LOG_DIR/${POOL_NAME}.log"
