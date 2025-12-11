set -exuo pipefail;

set -a && source "$WORKING_DIR/.env" && set +a

ss_http_exporter "$IP_UPSTREAM_NODE" 9100 "( sport = $PORT_NODE0 and dport = $PORT_UPSTREAM_NODE ) or ( sport = $PORT_UPSTREAM_NODE and dport = $PORT_NODE0 )"
