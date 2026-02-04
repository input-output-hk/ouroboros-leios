set -exuo pipefail

# Defaults for variables that may not be passed through sudo
: "${PORT_NODE0:=3002}"

cd "$NODE0_DIR"
export LEIOS_DB_PATH="leios.db"
cardano-node run \
  --config "config.json" \
  --topology "topology.json" \
  --database-path "db" \
  --socket-path "socket" \
  --host-addr 0.0.0.0 --port "$PORT_NODE0"
