#!/usr/bin/env bash
#
# Simple wrapper script to set defaults, check for requirements, and run the
# demo using process-compose
set -eo pipefail

# Set defaults for all environment variables
# These can be overridden by exporting them before running this script
set -a
# Traffic control (on by default, disable with TC=0). Without TC we
# bypass Linux network namespaces / sudo entirely and run the three
# nodes directly on distinct loopback addresses.
: "${TC:=1}"
: "${SOURCE_DIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
: "${WORKING_DIR:=tmp-demo-burst}"

# Data configuration
: "${DATA_DIR:=${SOURCE_DIR}/data}"
: "${CLUSTER_RUN:=${DATA_DIR}/2026-05-22-09-08-proto-devnet}"
: "${LEIOS_MANIFEST:=${SOURCE_DIR}/manifest.json}"

# Timing configuration
: "${REF_SLOT:=170}"
: "${SECONDS_UNTIL_REF_SLOT:=5}"
: "${BURST_SLOT:=219.9}"

# Node ports
: "${PORT_UPSTREAM_NODE:=3001}"
: "${PORT_NODE0:=3002}"
: "${PORT_DOWNSTREAM_NODE:=3003}"

if [ "$TC" = "1" ]; then
	# Node IPs (for network namespace addressing)
	: "${IP_UPSTREAM_NODE:=172.28.0.110}"
	: "${IP_NODE0:=172.28.0.120}"
	: "${IP_DOWNSTREAM_NODE:=172.28.0.130}"

	# Traffic control settings
	: "${RATE_UP_TO_N0:=10Mbps}"
	: "${DELAY_UP_TO_N0:=200ms}"
	: "${RATE_N0_TO_UP:=10Mbps}"
	: "${DELAY_N0_TO_UP:=200ms}"
	: "${RATE_N0_TO_DOWN:=10Mbps}"
	: "${DELAY_N0_TO_DOWN:=200ms}"
	: "${RATE_DOWN_TO_N0:=10Mbps}"
	: "${DELAY_DOWN_TO_N0:=200ms}"
else
	# Use distinct loopback aliases so each node's --host-addr (which
	# ouroboros-network also uses as the source IP for outbound sockets) does
	# not collide with another node's listening 4-tuple. With all three nodes
	# sharing 127.0.0.1, outbound connect() can return EADDRNOTAVAIL because
	# the kernel cannot assign (127.0.0.1:listener_port, 127.0.0.1:peer_port)
	# for the new socket while the listener still owns that port. Splitting
	# across the 127/8 range avoids the collision entirely.
	: "${IP_UPSTREAM_NODE:=127.1.0.1}"
	: "${IP_NODE0:=127.1.0.2}"
	: "${IP_DOWNSTREAM_NODE:=127.1.0.3}"
fi
set +a

# Check for required commands
REQUIRED_COMMANDS=(
  "process-compose"
  "sqlite3"
  "jq"
  "python"
  "cardano-node"
  "immdb-server"
  "leios-schedule-gen"
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
if [ "$TC" = "1" ]; then
	echo "  Traffic control: enabled TC=${TC} (${RATE_UP_TO_N0} / ${DELAY_UP_TO_N0})"
	PC_FILE="process-compose.yaml"
else
	echo "  Traffic control: disabled TC=${TC} (nodes on distinct loopback)"
	PC_FILE="process-compose-no-tc.yaml"
fi

process-compose --no-server -f "${SOURCE_DIR}/${PC_FILE}"
