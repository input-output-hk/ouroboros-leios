set -exuo pipefail

# Defaults for variables that may not be passed through sudo
: "${IP_UPSTREAM_NODE:=10.0.0.1}"
: "${PORT_UPSTREAM_NODE:=3001}"
: "${PORT_NODE0:=3002}"

ss_http_exporter "$IP_UPSTREAM_NODE" 9100 "( sport = $PORT_NODE0 and dport = $PORT_UPSTREAM_NODE ) or ( sport = $PORT_UPSTREAM_NODE and dport = $PORT_NODE0 )"
