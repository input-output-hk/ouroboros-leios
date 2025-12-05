# HTTP exporter for `ss`
# Dependencies:
# - ss (iproute2)
# - http_command
# - ss_to_prometheus
#
# Usage:
# ./ss_http_exporter.sh 127.0.0.1 9100 "dport :443"

# --- Configuration ---
LISTEN_ADDR=${1:-"0.0.0.0"}
LISTEN_PORT=${2:-9100}
FILTER=${3:-""}

http_command "$LISTEN_ADDR" "$LISTEN_PORT" "ss_prom $FILTER"
