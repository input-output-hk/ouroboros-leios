#!/usr/bin/env bash
#
# X-ray environment defaults. Sourced by run.sh and any integrating script.
# All variables can be overridden by the caller before sourcing this file.

: "${XRAY_SOURCE_DIR:=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
: "${WORKING_DIR:=$(pwd)/tmp-x-ray}"
: "${GRAFANA_SHARE:=$(dirname "$(dirname "$(command -v grafana)")")/share/grafana}"
: "${GRAFANA_INI:=${XRAY_SOURCE_DIR}/grafana.ini}"
: "${GRAFANA_HOMEPATH:=${XRAY_SOURCE_DIR}/grafana}"
: "${ALLOY_CONFIG:=${XRAY_SOURCE_DIR}/alloy}"
: "${PROMETHEUS_CONFIG:=${XRAY_SOURCE_DIR}/prometheus.yaml}"
: "${LOKI_CONFIG:=${XRAY_SOURCE_DIR}/loki.yaml}"
: "${SS_FILTER:=( sport = 3001 and dport = 3002 ) or ( sport = 3002 and dport = 3001 ) or ( sport = 3002 and dport = 3003 ) or ( sport = 3003 and dport = 3002 )}"
: "${DEMO_DASHBOARDS_DIR:=${WORKING_DIR}/demo-dashboards}"

XRAY_REQUIRED_COMMANDS=(prometheus loki grafana alloy ss_http_exporter process-compose)
