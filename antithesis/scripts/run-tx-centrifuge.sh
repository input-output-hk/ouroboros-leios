#!/usr/bin/env bash
# Run tx-centrifuge for load testing
# Waits for pool nodes to be ready, generates config, then runs tx-centrifuge

set -euo pipefail

echo "=== Starting tx-centrifuge ==="

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

# Copy genesis files alongside config (config.yaml uses relative paths)
cp "$SHARED_GENESIS_DIR/"*.json "$DATA_DIR/"
echo "  Genesis files copied"

# Copy node config for tx-centrifuge
if [ -f "$CONFIG_DIR/config.yaml" ]; then
    cp "$CONFIG_DIR/config.yaml" "$DATA_DIR/config.yaml"
elif [ -f "$CONFIG_DIR/config.json" ]; then
    cp "$CONFIG_DIR/config.json" "$DATA_DIR/config.yaml"
else
    echo "ERROR: No node config found in $CONFIG_DIR"
    exit 1
fi

# Copy utxo-keys
mkdir -p "$DATA_DIR/utxo-keys"
cp -r "$UTXO_KEYS_DIR/"* "$DATA_DIR/utxo-keys/"
chmod 400 "$DATA_DIR/utxo-keys"/*/*.skey

# Copy funds.json
cp "$CONFIG_DIR/funds.json" "$DATA_DIR/funds.json"

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

# Give nodes a bit more time to sync
echo "Waiting 10s for nodes to stabilize..."
sleep 10

# Query protocol parameters from node
echo "Querying protocol parameters..."
CARDANO_NODE_SOCKET_PATH="/pool1-data/socket" \
    cardano-cli conway query protocol-parameters \
    --testnet-magic 164 \
    --out-file "$DATA_DIR/pp.json" \
    || echo "WARNING: Could not query protocol parameters (will retry at startup)"

# Generate centrifuge config from template
echo "Generating centrifuge config..."
if [ -f "$CONFIG_DIR/centrifuge.template.json" ]; then
    export IP_POOL1 IP_POOL2 IP_POOL3
    export PORT_POOL1 PORT_POOL2 PORT_POOL3
    export TPS="${TPS:-100}"

    cat "$CONFIG_DIR/centrifuge.template.json" | \
        sed "s/\${IP_POOL1}/$IP_POOL1/g" | \
        sed "s/\${IP_POOL2}/$IP_POOL2/g" | \
        sed "s/\${IP_POOL3}/$IP_POOL3/g" | \
        sed "s/\${PORT_POOL1}/$PORT_POOL1/g" | \
        sed "s/\${PORT_POOL2}/$PORT_POOL2/g" | \
        sed "s/\${PORT_POOL3}/$PORT_POOL3/g" | \
        sed "s/\${TPS}/$TPS/g" | \
        jq '.nodeConfig = "/data/config.yaml"' | \
        jq '.protocolParametersFile = "/data/pp.json"' | \
        jq '.initial_inputs.params.signing_keys_file = "/data/funds.json"' | \
        jq '.workloads["synthetic-chain"].targets.pool1.addr = "'"$IP_POOL1"'"' \
        > "$DATA_DIR/centrifuge.json"
    echo "  centrifuge.json created"
else
    echo "ERROR: centrifuge.template.json not found"
    exit 1
fi

echo "Starting tx-centrifuge..."
cd "$DATA_DIR"
exec tx-centrifuge centrifuge.json
