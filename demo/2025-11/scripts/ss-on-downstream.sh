set -exuo pipefail

# Defaults for variables that may not be passed through sudo
: "${IP_DOWNSTREAM_NODE:=10.0.0.3}"
: "${PORT_NODE0:=3002}"
: "${PORT_DOWNSTREAM_NODE:=3003}"

ss_http_exporter "$IP_DOWNSTREAM_NODE" 9100 "( sport = $PORT_NODE0 and dport = $PORT_DOWNSTREAM_NODE ) or ( sport = $PORT_DOWNSTREAM_NODE and dport = $PORT_NODE0 )"
