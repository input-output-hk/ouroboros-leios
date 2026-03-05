set -exuo pipefail

ss_http_exporter "$IP_NODE0" 9100 "( dst = $IP_DOWNSTREAM_NODE ) or ( dst = $IP_UPSTREAM_NODE )"
