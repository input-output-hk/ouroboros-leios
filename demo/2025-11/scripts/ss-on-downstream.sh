set -exuo pipefail

ss_http_exporter "$IP_DOWNSTREAM_NODE" 9100 "( dst = $IP_NODE0 )"
