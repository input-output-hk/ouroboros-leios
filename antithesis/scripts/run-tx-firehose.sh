#!/usr/bin/env bash
# Run tx-firehose continuously for local devnet testing.

set -euo pipefail

echo "=== Starting tx-firehose ==="

DATA_DIR="${DATA_DIR:-/data}"
LOG_DIR="${LOG_DIR:-/logs}"
SOCKET_PATH="${CARDANO_NODE_SOCKET_PATH:-/pool1-data/socket}"
NETWORK_MAGIC="${CARDANO_NODE_NETWORK_MAGIC:-164}"
SIGNING_KEY_FILE="${TX_FIREHOSE_SIGNING_KEY_FILE:-/app/stake-delegators/delegator1/payment.skey}"
STAKING_KEY_FILE="${TX_FIREHOSE_STAKING_KEY_FILE:-/app/stake-delegators/delegator1/staking.skey}"
TPS="${TPS:-100}"
FEE="${TX_FIREHOSE_FEE:-1000000}"

mkdir -p "$DATA_DIR" "$LOG_DIR"

echo "Configuration:"
echo "  SOCKET_PATH: $SOCKET_PATH"
echo "  NETWORK_MAGIC: $NETWORK_MAGIC"
echo "  TPS: $TPS"
echo "  LOG_DIR: $LOG_DIR"

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

echo "Starting tx-firehose..."
exec tx-firehose \
    --socket-path "$SOCKET_PATH" \
    --testnet-magic "$NETWORK_MAGIC" \
    --signing-key-file "$SIGNING_KEY_FILE" \
    --staking-key-file "$STAKING_KEY_FILE" \
    --tps "$TPS" \
    --fee "$FEE" \
    >> "$LOG_DIR/tx-firehose.log" 2>&1
