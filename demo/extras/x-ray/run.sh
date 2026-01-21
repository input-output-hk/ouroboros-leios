#!/usr/bin/env bash
#
# Wrapper script to set defaults and run the x-ray observability stack using process-compose
set -eo pipefail

# Set defaults for all environment variables
# These can be overridden by:
# 1. Nix (via runtimeEnv in build.nix)
# 2. User exports before running this script
set -a
: "${WORKING_DIR:=tmp-x-ray}"
: "${SOURCE_DIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
: "${GRAFANA_INI:=${SOURCE_DIR}/grafana.ini}"
: "${GRAFANA_HOMEPATH:=${SOURCE_DIR}/grafana}"
: "${ALLOY_CONFIG:=${SOURCE_DIR}/alloy}"
: "${PROMETHEUS_CONFIG:=${SOURCE_DIR}/prometheus.yaml}"
: "${LOKI_CONFIG:=${SOURCE_DIR}/loki.yaml}"
# LOG_PATH should be absolute for best results (relative path for backwards compatibility)
: "${LOG_PATH:=../../leios-202511-demo/.tmp-leios-202511-demo/*/log}"
: "${SS_FILTER:=( sport = 3001 and dport = 3002 ) or ( sport = 3002 and dport = 3001 ) or ( sport = 3002 and dport = 3003 ) or ( sport = 3003 and dport = 3002 )}"
: "${GRAFANA_SHARE:=}"
set +a

# Warn if GRAFANA_SHARE is not set (required for Grafana to work)
if [ -z "${GRAFANA_SHARE}" ]; then
  echo "Warning: GRAFANA_SHARE not set. Grafana may not work correctly."
fi

# Check if WORKING_DIR already exists
if [ -d "$WORKING_DIR" ]; then
  echo "Working directory already exists: $WORKING_DIR"
  read -r -p "Remove and start fresh? (Y/n): " response
  if [[ "$response" =~ ^[Yy]$ || -z "$response" ]]; then
    echo "Removing existing working directory..."
    chmod a+w "${WORKING_DIR}"
    rm -rf "$WORKING_DIR"
  else
    echo "Continuing with existing working directory..."
  fi
fi

echo "Starting x-ray with process-compose..."
echo "  ALLOY_CONFIG: ${ALLOY_CONFIG}"
echo "  LOG_PATH: ${LOG_PATH}"
echo "  WORKING_DIR: ${WORKING_DIR}"

process-compose --no-server -f "${SOURCE_DIR}/process-compose.yaml"
