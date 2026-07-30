#!/usr/bin/env bash
# Randomized tx-firehose loop for Antithesis testing.
#
# Each iteration varies the submission rate and lifetime. Antithesis replaces
# /dev/urandom with a deterministic source, so the workload remains replayable
# while exposing different mempool and propagation timings.

set -euo pipefail

echo "=== Starting randomized tx-firehose loop ==="

DATA_DIR="${DATA_DIR:-/data}"
LOG_DIR="${LOG_DIR:-/logs}"
SOCKET_PATH="${CARDANO_NODE_SOCKET_PATH:-/pool1-data/socket}"
NETWORK_MAGIC="${CARDANO_NODE_NETWORK_MAGIC:-164}"
SIGNING_KEY_FILE="${TX_FIREHOSE_SIGNING_KEY_FILE:-/app/stake-delegators/delegator1/payment.skey}"
STAKING_KEY_FILE="${TX_FIREHOSE_STAKING_KEY_FILE:-/app/stake-delegators/delegator1/staking.skey}"
FEE="${TX_FIREHOSE_FEE:-1000000}"

TPS_MIN="${TPS_MIN:-100}"
TPS_MAX="${TPS_MAX:-10000}"
DURATION_MIN="${DURATION_MIN:-10}"
DURATION_MAX="${DURATION_MAX:-300}"
COOLDOWN_MIN="${COOLDOWN_MIN:-1}"
COOLDOWN_MAX="${COOLDOWN_MAX:-60}"
RESTART_BACKOFF_SECONDS="${RESTART_BACKOFF_SECONDS:-30}"

mkdir -p "$DATA_DIR" "$LOG_DIR"

echo "Configuration:"
echo "  SOCKET_PATH: $SOCKET_PATH"
echo "  NETWORK_MAGIC: $NETWORK_MAGIC"
echo "  TPS range: $TPS_MIN - $TPS_MAX"
echo "  DURATION range: ${DURATION_MIN}s - ${DURATION_MAX}s"
echo "  COOLDOWN range: ${COOLDOWN_MIN}s - ${COOLDOWN_MAX}s"
echo "  RESTART_BACKOFF_SECONDS: $RESTART_BACKOFF_SECONDS"

echo "Waiting for pool1 node socket..."
for i in $(seq 1 120); do
    if [ -S "$SOCKET_PATH" ]; then
        break
    fi
    if [ $((i % 10)) -eq 0 ]; then
        echo "  Waiting for pool1 socket... ($i/120)"
    fi
    sleep 1
done

if [ ! -S "$SOCKET_PATH" ]; then
    echo "ERROR: Node socket not found: $SOCKET_PATH"
    exit 1
fi

rand_range() {
    local min=$1
    local max=$2
    local range=$((max - min + 1))
    local raw
    raw=$(od -An -tu4 -N4 /dev/urandom | tr -d ' ')
    echo $(( (raw % range) + min ))
}

iteration=0
while true; do
    iteration=$((iteration + 1))
    tps=$(rand_range "$TPS_MIN" "$TPS_MAX")
    duration=$(rand_range "$DURATION_MIN" "$DURATION_MAX")
    cooldown=$(rand_range "$COOLDOWN_MIN" "$COOLDOWN_MAX")

    echo "=== Iteration $iteration: tps=$tps duration=${duration}s cooldown=${cooldown}s ==="
    echo "  Running tx-firehose for ${duration}s..."

    tx-firehose \
        --socket-path "$SOCKET_PATH" \
        --testnet-magic "$NETWORK_MAGIC" \
        --signing-key-file "$SIGNING_KEY_FILE" \
        --staking-key-file "$STAKING_KEY_FILE" \
        --tps "$tps" \
        --fee "$FEE" \
        >> "$LOG_DIR/tx-firehose.log" 2>&1 &
    FIREHOSE_PID=$!

    sleep "$duration"

    if kill -0 "$FIREHOSE_PID" 2>/dev/null; then
        kill "$FIREHOSE_PID" 2>/dev/null || true
        wait "$FIREHOSE_PID" 2>/dev/null || true
        echo "  tx-firehose stopped after ${duration}s"
        echo "  Cooling down for ${cooldown}s..."
        sleep "$cooldown"
    else
        wait "$FIREHOSE_PID" 2>/dev/null || true
        echo "  tx-firehose exited before duration elapsed"
        echo "  Waiting ${RESTART_BACKOFF_SECONDS}s before restart..."
        sleep "$RESTART_BACKOFF_SECONDS"
    fi
done
