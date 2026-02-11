#!/bin/bash
# Run tx-generator for load testing
# Waits for pool nodes to be ready, generates config, then runs tx-generator

set -euo pipefail

echo "=== Starting tx-generator ==="

DATA_DIR="${DATA_DIR:-/data}"
CONFIG_DIR="${CONFIG_DIR:-/app/config}"
UTXO_KEYS_DIR="${UTXO_KEYS_DIR:-/app/utxo-keys}"
SHARED_GENESIS_DIR="${SHARED_GENESIS_DIR:-/shared-genesis}"

# Node connection details
IP_POOL1="${IP_POOL1:-172.28.0.10}"
IP_POOL2="${IP_POOL2:-172.28.0.20}"
IP_POOL3="${IP_POOL3:-172.28.0.30}"
PORT_POOL1="${PORT_POOL1:-3001}"
PORT_POOL2="${PORT_POOL2:-3002}"
PORT_POOL3="${PORT_POOL3:-3003}"

echo "Configuration:"
echo "  DATA_DIR: $DATA_DIR"
echo "  Pool1: $IP_POOL1:$PORT_POOL1"
echo "  Pool2: $IP_POOL2:$PORT_POOL2"
echo "  Pool3: $IP_POOL3:$PORT_POOL3"

# Create data directory
mkdir -p "$DATA_DIR"

# Wait for genesis files from pool1
echo "Waiting for genesis files..."
for i in $(seq 1 120); do
    if [ -f "$SHARED_GENESIS_DIR/.genesis-ready" ]; then
        break
    fi
    echo "  Waiting for genesis... ($i/120)"
    sleep 1
done

if [ ! -f "$SHARED_GENESIS_DIR/.genesis-ready" ]; then
    echo "ERROR: Timeout waiting for genesis files"
    exit 1
fi

# Copy genesis files
mkdir -p "$DATA_DIR/genesis"
cp "$SHARED_GENESIS_DIR/"*.json "$DATA_DIR/genesis/"
echo "  Genesis files copied"

# Copy config for cardano-cli
cp "$CONFIG_DIR/config.json" "$DATA_DIR/config.json"

# Copy utxo-keys
mkdir -p "$DATA_DIR/utxo-keys"
cp -r "$UTXO_KEYS_DIR/"* "$DATA_DIR/utxo-keys/"
chmod 400 "$DATA_DIR/utxo-keys"/*/*.skey

# Wait for at least one pool to be ready (check TCP connectivity)
echo "Waiting for pool nodes to be ready..."
wait_for_node() {
    local ip=$1
    local port=$2
    local name=$3
    for i in $(seq 1 120); do
        if nc -z "$ip" "$port" 2>/dev/null || socat -u OPEN:/dev/null TCP:"$ip:$port",connect-timeout=1 2>/dev/null; then
            echo "  $name is ready at $ip:$port"
            return 0
        fi
        if [ $((i % 10)) -eq 0 ]; then
            echo "  Waiting for $name... ($i/120)"
        fi
        sleep 1
    done
    echo "  WARNING: $name not reachable after 120s"
    return 1
}

wait_for_node "$IP_POOL1" "$PORT_POOL1" "pool1" || true
wait_for_node "$IP_POOL2" "$PORT_POOL2" "pool2" || true
wait_for_node "$IP_POOL3" "$PORT_POOL3" "pool3" || true

# Generate tx-generator config from template
echo "Generating tx-generator config..."
if [ -f "$CONFIG_DIR/gen.template.json" ]; then
    # Substitute environment variables in template
    export IP_NODE1="$IP_POOL1"
    export IP_NODE2="$IP_POOL2"
    export IP_NODE3="$IP_POOL3"
    export PORT_NODE1="$PORT_POOL1"
    export PORT_NODE2="$PORT_POOL2"
    export PORT_NODE3="$PORT_POOL3"

    # Use envsubst to substitute variables, or sed for simple cases
    cat "$CONFIG_DIR/gen.template.json" | \
        sed "s/\${IP_NODE1}/$IP_POOL1/g" | \
        sed "s/\${IP_NODE2}/$IP_POOL2/g" | \
        sed "s/\${IP_NODE3}/$IP_POOL3/g" | \
        sed "s/\${PORT_NODE1}/$PORT_POOL1/g" | \
        sed "s/\${PORT_NODE2}/$PORT_POOL2/g" | \
        sed "s/\${PORT_NODE3}/$PORT_POOL3/g" | \
        jq '.localNodeSocketPath = null' | \
        jq '.nodeConfigFile = "/data/config.json"' | \
        jq '.sigKey = "/data/utxo-keys/utxo1/utxo.skey"' \
        > "$DATA_DIR/gen.json"
    echo "  gen.json created"
else
    echo "ERROR: gen.template.json not found"
    exit 1
fi

# Give nodes a bit more time to sync
echo "Waiting 10s for nodes to stabilize..."
sleep 10

echo "Starting tx-generator..."
exec tx-generator run-script \
    --config "$DATA_DIR/gen.json" \
    --genesis-alonzo "$DATA_DIR/genesis/alonzo-genesis.json" \
    --genesis-conway "$DATA_DIR/genesis/conway-genesis.json" \
    --genesis-shelley "$DATA_DIR/genesis/shelley-genesis.json"
