set -exuo pipefail

cd "$NODE0_DIR"
export LEIOS_VOL_DB_PATH="leios.db.vol"
export LEIOS_IMM_DB_PATH="leios.db.imm"
cardano-node run \
  --config "config.json" \
  --topology "topology.json" \
  --database-path "db" \
  --socket-path "socket" \
  --host-addr "${IP_NODE0:-0.0.0.0}" --port "$PORT_NODE0"
