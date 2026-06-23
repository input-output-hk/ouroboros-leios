#!/usr/bin/env bash
#
# Orchestrate a Leios testnet relay alongside the X-ray observability
# stack (Prometheus + Loki + Grafana via Alloy) using process-compose.
# For just the node, run ./run-node.sh instead.

set -eo pipefail

# Set defaults for all environment variables.
# Override by exporting before invoking this script.
set -a
: "${WORKING_DIR:=$(pwd)/tmp-testnet}"
: "${SOURCE_DIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
: "${PORT:=3010}"
: "${HOST_ADDR:=0.0.0.0}"
: "${METRICS_PORT:=12798}"
# X-ray observability (on by default, disable with XRAY=0)
: "${XRAY:=1}"
: "${XRAY_SOURCE_DIR:=${SOURCE_DIR}/../demo/extras/x-ray}"
set +a

# Check for required commands
REQUIRED_COMMANDS=(
  "process-compose"
  "cardano-node"
  "cardano-cli"
  "envsubst"
  "jq"
)
MISSING_COMMANDS=()
for cmd in "${REQUIRED_COMMANDS[@]}"; do
  if ! command -v "$cmd" &>/dev/null; then
    MISSING_COMMANDS+=("$cmd")
  fi
done
if [ ${#MISSING_COMMANDS[@]} -gt 0 ]; then
  echo "Error: The following required commands are not available:"
  for cmd in "${MISSING_COMMANDS[@]}"; do
    echo "  - $cmd"
  done
  echo ""
  echo "Please install the missing commands or use nix:"
  echo "  nix run github:input-output-hk/ouroboros-leios#leios-testnet-relay"
  exit 1
fi

mkdir -p "$WORKING_DIR"

# Generate Alloy config so its scrape targets resolve to the node's
# actual Prometheus endpoint.
if [ "$XRAY" = "1" ]; then
  export ALLOY_CONFIG="${WORKING_DIR}/config.alloy"
  envsubst <"${SOURCE_DIR}/config/alloy.template" >"${ALLOY_CONFIG}"
fi

echo "Starting Leios testnet relay"
echo "  binary:     $(cardano-node --version 2>&1 | head -1)"
echo "  workdir:    $WORKING_DIR"
echo "  bind:       $HOST_ADDR:$PORT"
echo "  metrics:    127.0.0.1:$METRICS_PORT"

XRAY_COMPOSE=()
if [ "$XRAY" = "1" ]; then
  set -a
  # Reuse the proto-devnet dashboards until we ship testnet-specific ones.
  : "${DEMO_DASHBOARDS_DIR:=${SOURCE_DIR}/../demo/proto-devnet/config/dashboards}"
  # shellcheck source=/dev/null
  source "${XRAY_SOURCE_DIR}/env.sh"
  set +a
  XRAY_COMPOSE=(-f "${XRAY_SOURCE_DIR}/process-compose.yaml")
  echo "  X-ray:      enabled XRAY=${XRAY} (Grafana at http://localhost:3000)"
else
  echo "  X-ray:      disabled XRAY=${XRAY}"
fi

process-compose --no-server \
  -f "${SOURCE_DIR}/process-compose.yaml" \
  "${XRAY_COMPOSE[@]}"
