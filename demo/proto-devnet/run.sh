#!/usr/bin/env bash
set -eo pipefail

# Simple wrapper script to run the proto-devnet demo using process-compose
# This script sets defaults and runs process-compose

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
cd "$SCRIPT_DIR"

# Check for required commands
REQUIRED_COMMANDS=(
	"process-compose"
	"cardano-node"
	"cardano-cli"
	"sqlite3"
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
	echo "  nix run github:input-output-hk/ouroboros-leios#demo-proto-devnet"
	exit 1
fi

# Set defaults for all environment variables
# These can be overridden by exporting them before running this script
set -a
: "${WORKING_DIR:=devnet}"
: "${SCRIPTS:=./scripts}"
: "${CARDANO_NODE:=cardano-node}"
: "${CARDANO_CLI:=cardano-cli}"
: "${CONFIG_DIR:=config}"
: "${LEIOS_SCHEMA:=../2025-11/data/leios-schema.sql}"
: "${IP_NODE1:=0.0.0.0}"
: "${PORT_NODE1:=3001}"
: "${IP_NODE2:=0.0.0.0}"
: "${PORT_NODE2:=3002}"
: "${IP_NODE3:=0.0.0.0}"
: "${PORT_NODE3:=3003}"
set +a

# Run process-compose
echo "Starting proto-devnet with process-compose..."
process-compose --no-server -f process-compose.yaml
