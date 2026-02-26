#!/usr/bin/env bash
# Randomized tx-generator loop for Antithesis testing
#
# Runs tx-generator in an infinite loop with randomized parameters:
#   - tx_count: 100 to 100,000
#   - tps: 100 to 10,000
#   - cooldown: 1 to 60 seconds between batches
#
# Antithesis replaces /dev/urandom with a deterministic source it can
# learn from and replay, enabling guided exploration of load patterns.

set -euo pipefail

echo "=== Starting randomized tx-generator loop ==="

DATA_DIR="${DATA_DIR:-/data}"
CONFIG_DIR="${CONFIG_DIR:-/app/config}"
UTXO_KEYS_DIR="${UTXO_KEYS_DIR:-/app/utxo-keys}"
SHARED_GENESIS_DIR="${SHARED_GENESIS_DIR:-/shared-genesis}"

# Node connection details (hostnames in Antithesis, IPs locally)
IP_POOL1="${IP_POOL1:-pool1}"
IP_POOL2="${IP_POOL2:-pool2}"
IP_POOL3="${IP_POOL3:-pool3}"
PORT_POOL1="${PORT_POOL1:-3001}"
PORT_POOL2="${PORT_POOL2:-3002}"
PORT_POOL3="${PORT_POOL3:-3003}"

# Randomization ranges
TX_COUNT_MIN="${TX_COUNT_MIN:-100}"
TX_COUNT_MAX="${TX_COUNT_MAX:-100000}"
TPS_MIN="${TPS_MIN:-100}"
TPS_MAX="${TPS_MAX:-10000}"
COOLDOWN_MIN="${COOLDOWN_MIN:-1}"
COOLDOWN_MAX="${COOLDOWN_MAX:-60}"

echo "Configuration:"
echo "  DATA_DIR: $DATA_DIR"
echo "  Pool1: $IP_POOL1:$PORT_POOL1"
echo "  Pool2: $IP_POOL2:$PORT_POOL2"
echo "  Pool3: $IP_POOL3:$PORT_POOL3"
echo "  TX_COUNT range: $TX_COUNT_MIN - $TX_COUNT_MAX"
echo "  TPS range: $TPS_MIN - $TPS_MAX"
echo "  COOLDOWN range: ${COOLDOWN_MIN}s - ${COOLDOWN_MAX}s"

# --- One-time initialization (same as run-tx-generator.sh) ---

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

cp "$SHARED_GENESIS_DIR/"*.json "$DATA_DIR/"
echo "  Genesis files copied"

# Copy node config
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

# Wait for pool nodes
echo "Waiting for pool nodes to be ready..."
wait_for_node() {
    local host=$1
    local port=$2
    local name=$3
    for i in $(seq 1 120); do
        if nc -z "$host" "$port" 2>/dev/null || socat -u OPEN:/dev/null TCP:"$host:$port",connect-timeout=1 2>/dev/null; then
            echo "  $name is ready at $host:$port"
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

echo "Waiting 10s for nodes to stabilize..."
sleep 10

# --- Helper: generate random integer in [min, max] from /dev/urandom ---
rand_range() {
    local min=$1
    local max=$2
    local range=$((max - min + 1))
    local raw
    raw=$(od -An -tu4 -N4 /dev/urandom | tr -d ' ')
    echo $(( (raw % range) + min ))
}

# --- Main loop ---
iteration=0
while true; do
    iteration=$((iteration + 1))

    tx_count=$(rand_range "$TX_COUNT_MIN" "$TX_COUNT_MAX")
    tps=$(rand_range "$TPS_MIN" "$TPS_MAX")
    cooldown=$(rand_range "$COOLDOWN_MIN" "$COOLDOWN_MAX")

    echo "=== Iteration $iteration: tx_count=$tx_count tps=$tps cooldown=${cooldown}s ==="

    # Generate config with randomized parameters
    if [ ! -f "$CONFIG_DIR/gen.template.json" ]; then
        echo "ERROR: gen.template.json not found"
        exit 1
    fi

    cat "$CONFIG_DIR/gen.template.json" | \
        sed "s/\${IP_NODE1}/$IP_POOL1/g" | \
        sed "s/\${IP_NODE2}/$IP_POOL2/g" | \
        sed "s/\${IP_NODE3}/$IP_POOL3/g" | \
        sed "s/\${PORT_NODE1}/$PORT_POOL1/g" | \
        sed "s/\${PORT_NODE2}/$PORT_POOL2/g" | \
        sed "s/\${PORT_NODE3}/$PORT_POOL3/g" | \
        jq --argjson tx_count "$tx_count" \
           --argjson tps "$tps" \
           '.tx_count = $tx_count | .tps = $tps' | \
        jq '.localNodeSocketPath = "/pool1-data/socket"' | \
        jq '.nodeConfigFile = "/data/config.yaml"' | \
        jq '.sigKey = "/data/utxo-keys/utxo1/utxo.skey"' \
        > "$DATA_DIR/gen.json"

    echo "  gen.json created: tx_count=$tx_count, tps=$tps"

    # Run tx-generator (exits after batch completes)
    echo "  Running tx-generator..."
    tx-generator json_highlevel \
        "$DATA_DIR/gen.json" \
        --nodeConfig "$DATA_DIR/config.yaml" \
        || echo "  tx-generator exited with error (continuing)"

    echo "  Batch complete. Cooling down for ${cooldown}s..."
    sleep "$cooldown"
done
