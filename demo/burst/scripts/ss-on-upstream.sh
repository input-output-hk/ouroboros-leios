set -exuo pipefail

ss_http_exporter "$IP_UPSTREAM_NODE" 9100 "( dst = $IP_NODE0 )" &
{ while true; do date; ss -i -m -t sport = :3001; sleep 0.1s; done; } 2>&1 >${WORKING_DIR}/ss-upstream.log
