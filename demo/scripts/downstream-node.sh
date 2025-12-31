set -exuo pipefail
set -a && source "$WORKING_DIR/.env" && set +a

cd "$DOWNSTREAM_NODE_DIR"
export LEIOS_DB_PATH="leios.db"
"$CARDANO_NODE" run \
  --config "config.json" \
  --topology "topology.json" \
  --database-path "db" \
  --socket-path "socket" \
  --host-addr "0.0.0.0" --port "$PORT_DOWNSTREAM_NODE"
