set -exuo pipefail

# Defaults for variables that may not be passed through sudo
: "${PORT_UPSTREAM_NODE:=3001}"

cd "$UPSTREAM_NODE_DIR"
immdb-server \
  --db "immutable/" \
  --config "config.json" \
  --initial-slot "$REF_SLOT" \
  --initial-time "$ONSET_OF_REF_SLOT" \
  --leios-schedule "schedule.json" \
  --leios-db "leios.db" \
  --address "0.0.0.0" \
  --port "$PORT_UPSTREAM_NODE"
