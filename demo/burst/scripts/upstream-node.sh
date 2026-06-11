set -exuo pipefail

cd "$UPSTREAM_NODE_DIR"
immdb-server \
  --db "immutable/" \
  --config "config.json" \
  --initial-slot "$REF_SLOT" \
  --initial-time "$ONSET_OF_REF_SLOT" \
  --leios-schedule "schedule.json" \
  --leios-db "leios.db" \
  --address "${IP_UPSTREAM_NODE:-0.0.0.0}" \
  --port 3001
