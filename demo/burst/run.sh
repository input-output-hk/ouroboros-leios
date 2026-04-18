#!/usr/bin/env bash
#
# Simple wrapper script to set defaults, check for requirements, and run the
# demo using process-compose
set -eo pipefail

# Set defaults for all environment variables
# These can be overridden by exporting them before running this script
set -a
: "${WORKING_DIR:=tmp-demo-burst}"
: "${SOURCE_DIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"

# Data configuration
: "${DATA_DIR:=${SOURCE_DIR}/data}"
: "${CLUSTER_RUN:=${DATA_DIR}/2025-10-10-13-29-24641-1050-50-blocks-50-coay-sup}"
: "${LEIOS_MANIFEST:=${SOURCE_DIR}/manifest.json}"

# Timing configuration
: "${REF_SLOT:=120}"
: "${SECONDS_UNTIL_REF_SLOT:=10}"

# Node ports
: "${PORT_UPSTREAM_NODE:=3001}"
: "${PORT_NODE0:=3002}"
: "${PORT_DOWNSTREAM_NODE:=3003}"

# Node IPs (for network namespace addressing)
: "${IP_UPSTREAM_NODE:=10.0.0.1}"
: "${IP_NODE0:=10.0.0.2}"
: "${IP_DOWNSTREAM_NODE:=10.0.0.3}"

# Traffic control settings
: "${RATE:=10mbit}"
: "${DELAY:=200}"
set +a

# Check for required commands
REQUIRED_COMMANDS=(
  "process-compose"
  "sqlite3"
  "jq"
  "python"
  "cardano-node"
  "immdb-server"
  "leiosdemo202510"
  "ss_http_exporter"
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
  echo "  nix run github:input-output-hk/ouroboros-leios#demo-burst"
  exit 1
fi

# Check if WORKING_DIR already exists
if [ -d "$WORKING_DIR" ]; then
  echo "Working directory already exists: $WORKING_DIR"
  read -r -p "Remove and re-initialize? (Y/n): " response
  if [[ "$response" =~ ^[Yy]$ || -z "$response" ]]; then
    chmod a+w -R "$WORKING_DIR" 2>/dev/null || true
    rm -rf "$WORKING_DIR"
  else
    echo "Aborting."
    exit 0
  fi
fi
echo "Initializing burst demo in $WORKING_DIR"

# Create working directory
mkdir -p "$WORKING_DIR"

# Copy genesis files
if [ ! -d "$WORKING_DIR/genesis" ]; then
  echo "Copying genesis"
  cp -fr "$CLUSTER_RUN/genesis" "$WORKING_DIR/genesis"
  chmod -R +rw "$WORKING_DIR/genesis"
fi

# Set derived variables
export UPSTREAM_NODE_DIR="$WORKING_DIR/upstream-node"
export NODE0_DIR="$WORKING_DIR/node0"
export DOWNSTREAM_NODE_DIR="$WORKING_DIR/downstream-node"
export ONSET_OF_REF_SLOT=$(($(date +%s) + SECONDS_UNTIL_REF_SLOT))

echo "Starting burst demo with process-compose..."
echo "  WORKING_DIR: $WORKING_DIR"
echo "  CLUSTER_RUN: $CLUSTER_RUN"
echo "  REF_SLOT: $REF_SLOT"
echo "  Traffic control: ${RATE} / ${DELAY}ms"

cleanup() {
  echo "Cleaning up network namespaces..."
  sudo ip netns del "leios-experiment:upstream" 2>/dev/null || true
  sudo ip netns del "leios-experiment:node0" 2>/dev/null || true
  sudo ip netns del "leios-experiment:downstream" 2>/dev/null || true
  # Clean up host-side veth interfaces in case they weren't removed with the namespace
  sudo ip link del "host->up" 2>/dev/null || true
  sudo ip link del "host->n0" 2>/dev/null || true
  sudo ip link del "host->down" 2>/dev/null || true
}
trap cleanup EXIT

process-compose --no-server -f "${SOURCE_DIR}/process-compose.yaml"
