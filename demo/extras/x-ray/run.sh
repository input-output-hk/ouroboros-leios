#!/usr/bin/env bash
#
# Wrapper script to set defaults and run the x-ray observability stack using process-compose
set -eo pipefail

# Set defaults for all environment variables (can be overridden before sourcing)
: "${SOURCE_DIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
: "${XRAY_SOURCE_DIR:=${SOURCE_DIR}}"
set -a
source "${SOURCE_DIR}/env.sh"
set +a

# Check for required commands
XRAY_MISSING=()
for cmd in "${XRAY_REQUIRED_COMMANDS[@]}"; do
  if ! command -v "$cmd" &>/dev/null; then
    XRAY_MISSING+=("$cmd")
  fi
done

if [ "${#XRAY_MISSING[@]}" -gt 0 ]; then
  echo "Error: The following required commands are not available:"
  for cmd in "${XRAY_MISSING[@]}"; do
    echo "  - $cmd"
  done
  echo ""
  echo "Please install the missing commands or use nix:"
  echo "  nix run github:input-output-hk/ouroboros-leios#x-ray"
  exit 1
fi

# Check if WORKING_DIR already exists
if [ -d "$WORKING_DIR" ]; then
  echo "Working directory already exists: $WORKING_DIR"
  read -r -p "Remove and start fresh? (Y/n): " response
  if [[ "$response" =~ ^[Yy]$ || -z "$response" ]]; then
    echo "Removing existing working directory..."
    chmod a+w "${WORKING_DIR}"
    rm -rf "$WORKING_DIR"
    mkdir "$WORKING_DIR"
  else
    echo "Continuing with existing working directory..."
  fi
fi

mkdir -p "$WORKING_DIR"

echo "Starting x-ray with process-compose..."
echo "  ALLOY_CONFIG: ${ALLOY_CONFIG}"
echo "  WORKING_DIR: ${WORKING_DIR}"
process-compose --no-server -f "${SOURCE_DIR}/process-compose.yaml"
