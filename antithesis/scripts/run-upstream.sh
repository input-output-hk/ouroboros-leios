#!/bin/bash
# Run immdb-server (upstream mock peer)

set -euo pipefail

DATA_DIR="${DATA_DIR:-/data}"
LOG_DIR="${LOG_DIR:-/logs}"
PORT="${PORT:-3001}"

# Timing configuration
REF_SLOT="${REF_SLOT:-11}"
ONSET_OF_REF_SLOT="${ONSET_OF_REF_SLOT:-$(date +%s)}"

echo "=== Starting immdb-server (upstream) ==="

# Setup WAN emulation if enabled
if [ "${ENABLE_WAN_EMULATION:-false}" = "true" ]; then
    echo "Setting up WAN emulation..."
    /app/scripts/setup-wan-emulation.sh || echo "WAN emulation setup failed (continuing anyway)"
fi

# Ensure log directory exists
mkdir -p "$LOG_DIR"

echo "Configuration:"
echo "  DATA_DIR: $DATA_DIR"
echo "  LOG_DIR: $LOG_DIR"
echo "  PORT: $PORT"
echo "  REF_SLOT: $REF_SLOT"
echo "  ONSET_OF_REF_SLOT: $ONSET_OF_REF_SLOT"

# Run immdb-server with tee to both stdout and log file
exec immdb-server \
    --db "$DATA_DIR/immutable/" \
    --config "$DATA_DIR/config.json" \
    --initial-slot "$REF_SLOT" \
    --initial-time "$ONSET_OF_REF_SLOT" \
    --leios-schedule "$DATA_DIR/schedule.json" \
    --leios-db "$DATA_DIR/leios.db" \
    --address "0.0.0.0" \
    --port "$PORT" \
    2>&1 | tee "$LOG_DIR/upstream-node.log"
