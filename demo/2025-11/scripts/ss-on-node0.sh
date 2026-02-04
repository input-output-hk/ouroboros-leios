set -exuo pipefail

# Defaults for variables that may not be passed through sudo
: "${IP_NODE0:=10.0.0.2}"
: "${PORT_NODE0:=3002}"
: "${PORT_UPSTREAM_NODE:=3001}"
: "${PORT_DOWNSTREAM_NODE:=3003}"

ss_http_exporter "$IP_NODE0" 9100 "( sport = $PORT_NODE0 and dport = $PORT_DOWNSTREAM_NODE ) or ( sport = $PORT_DOWNSTREAM_NODE and dport = $PORT_NODE0 ) or ( sport = $PORT_NODE0 and dport = $PORT_UPSTREAM_NODE ) or ( sport = $PORT_UPSTREAM_NODE and dport = $PORT_NODE0 )"
