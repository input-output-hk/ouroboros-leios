set -exuo pipefail
set -a && source "$WORKING_DIR/.env" && set +a

if [ -d "$DOWNSTREAM_NODE_DIR" ]; then
  echo "Removing old $DOWNSTREAM_NODE_DIR"
  rm -fr "$DOWNSTREAM_NODE_DIR"
fi

mkdir "$DOWNSTREAM_NODE_DIR"
echo "Working directory created for downstream-node: $DOWNSTREAM_NODE_DIR"

cat "$DATA_DIR/leios-schema.sql" | sqlite3 "$DOWNSTREAM_NODE_DIR/leios.db"

jq \
  --argjson port "$PORT_NODE0" \
  --arg address "$IP_NODE0" \
  '.localRoots[0].accessPoints[0].port = $port | .localRoots[0].accessPoints[0].address = $address' \
  "$DATA_DIR/topology.template.json" >"$DOWNSTREAM_NODE_DIR/topology.json"

cp -f "$DATA_DIR/downstream-node/config.json" "$DOWNSTREAM_NODE_DIR/config.json"
