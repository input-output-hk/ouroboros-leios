set -exuo pipefail
set -a && source "$WORKING_DIR/.env" && set +a

if [ -d "$NODE0_DIR" ]; then
  echo "Removing old $NODE0_DIR"
  rm -fr "$NODE0_DIR"
fi

mkdir "$NODE0_DIR"
echo "Working directory created for node0: $NODE0_DIR"

cat "$DATA_DIR/leios-schema.sql" | sqlite3 "$NODE0_DIR/leios.db"

jq \
  --argjson port "$PORT_UPSTREAM_NODE" \
  --arg address "$IP_UPSTREAM_NODE" \
  '.localRoots[0].accessPoints[0].port = $port | .localRoots[0].accessPoints[0].address = $address' \
  "$DATA_DIR/topology.template.json" >"$NODE0_DIR/topology.json"

cp -f "$DATA_DIR/node0/config.json" "$NODE0_DIR/config.json"
