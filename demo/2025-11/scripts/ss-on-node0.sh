set -exuo pipefail

ss_http_exporter "$IP_NODE0" 9100 "( dst = $IP_DOWNSTREAM_NODE ) or ( dst = $IP_UPSTREAM_NODE )" &
{ while true; do date; ss -i -m -t sport = :3001; sleep 0.1s; done; } 2>&1 >${WORKING_DIR}/ss-node0.log
