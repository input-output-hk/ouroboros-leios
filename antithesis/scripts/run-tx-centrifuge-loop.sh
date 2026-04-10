#!/usr/bin/env bash
# Randomized tx-centrifuge loop for Antithesis testing
#
# Runs tx-centrifuge in an infinite loop with randomized parameters:
#   - tps: 100 to 10,000
#   - duration: 10 to 300 seconds per run
#   - cooldown: 1 to 60 seconds between runs
#
# Antithesis replaces /dev/urandom with a deterministic source it can
# learn from and replay, enabling guided exploration of load patterns.

set -euo pipefail

echo "=== Starting randomized tx-centrifuge loop ==="

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
TPS_MIN="${TPS_MIN:-100}"
TPS_MAX="${TPS_MAX:-10000}"
DURATION_MIN="${DURATION_MIN:-10}"
DURATION_MAX="${DURATION_MAX:-300}"
COOLDOWN_MIN="${COOLDOWN_MIN:-1}"
COOLDOWN_MAX="${COOLDOWN_MAX:-60}"

echo "Configuration:"
echo "  DATA_DIR: $DATA_DIR"
echo "  Pool1: $IP_POOL1:$PORT_POOL1"
echo "  Pool2: $IP_POOL2:$PORT_POOL2"
echo "  Pool3: $IP_POOL3:$PORT_POOL3"
echo "  TPS range: $TPS_MIN - $TPS_MAX"
echo "  DURATION range: ${DURATION_MIN}s - ${DURATION_MAX}s"
echo "  COOLDOWN range: ${COOLDOWN_MIN}s - ${COOLDOWN_MAX}s"

# --- One-time initialization (same as run-tx-centrifuge.sh) ---

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

# Copy funds.json
cp "$CONFIG_DIR/funds.json" "$DATA_DIR/funds.json"

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

# Query protocol parameters from node
echo "Querying protocol parameters..."
CARDANO_NODE_SOCKET_PATH="/pool1-data/socket" \
    cardano-cli conway query protocol-parameters \
    --testnet-magic 164 \
    --out-file "$DATA_DIR/pp.json" \
    || echo "WARNING: Could not query protocol parameters (will retry at startup)"

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

    tps=$(rand_range "$TPS_MIN" "$TPS_MAX")
    duration=$(rand_range "$DURATION_MIN" "$DURATION_MAX")
    cooldown=$(rand_range "$COOLDOWN_MIN" "$COOLDOWN_MAX")

    echo "=== Iteration $iteration: tps=$tps duration=${duration}s cooldown=${cooldown}s ==="

    # Generate config with randomized tps
    if [ ! -f "$CONFIG_DIR/centrifuge.template.json" ]; then
        echo "ERROR: centrifuge.template.json not found"
        exit 1
    fi

    cat "$CONFIG_DIR/centrifuge.template.json" | \
        sed "s/\${IP_POOL1}/$IP_POOL1/g" | \
        sed "s/\${IP_POOL2}/$IP_POOL2/g" | \
        sed "s/\${IP_POOL3}/$IP_POOL3/g" | \
        sed "s/\${PORT_POOL1}/$PORT_POOL1/g" | \
        sed "s/\${PORT_POOL2}/$PORT_POOL2/g" | \
        sed "s/\${PORT_POOL3}/$PORT_POOL3/g" | \
        sed "s/\${TPS}/$tps/g" | \
        jq '.nodeConfig = "/data/config.yaml"' | \
        jq '.protocolParametersFile = "/data/pp.json"' | \
        jq '.initial_inputs.params.signing_keys_file = "/data/funds.json"' | \
        jq '.workloads["synthetic-chain"].targets.pool1.addr = "'"$IP_POOL1"'"' \
        > "$DATA_DIR/centrifuge.json"

    echo "  centrifuge.json created: tps=$tps"

    # Run tx-centrifuge for the randomized duration, then stop it
    echo "  Running tx-centrifuge for ${duration}s..."
    cd "$DATA_DIR"
    tx-centrifuge centrifuge.json &
    CENTRIFUGE_PID=$!

    sleep "$duration"

    if kill -0 "$CENTRIFUGE_PID" 2>/dev/null; then
        kill "$CENTRIFUGE_PID" 2>/dev/null || true
        wait "$CENTRIFUGE_PID" 2>/dev/null || true
        echo "  tx-centrifuge stopped after ${duration}s"
    else
        echo "  tx-centrifuge exited before duration elapsed"
    fi

    echo "  Run complete. Cooling down for ${cooldown}s..."
    sleep "$cooldown"
done
