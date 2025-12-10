set -exuo pipefail
set -a && source "$WORKING_DIR/.env" && set +a

cd "$UPSTREAM_NODE_DIR"
$IMMDB_SERVER \
  --db "immutable/" \
  --config "config.json" \
  --initial-slot "$REF_SLOT" \
  --initial-time "$ONSET_OF_REF_SLOT" \
  --leios-schedule "schedule.json" \
  --leios-db "leios.db" \
  --address "0.0.0.0"
--port "$PORT_UPSTREAM_NODE"
