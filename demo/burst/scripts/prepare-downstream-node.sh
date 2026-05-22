set -exuo pipefail

if [ -d "$DOWNSTREAM_NODE_DIR" ]; then
  echo "Removing old $DOWNSTREAM_NODE_DIR"
  rm -fr "$DOWNSTREAM_NODE_DIR"
fi

mkdir "$DOWNSTREAM_NODE_DIR"
echo "Working directory created for downstream-node: $DOWNSTREAM_NODE_DIR"

jq \
  --argjson port "$PORT_NODE0" \
  --arg address "$IP_NODE0" \
  '.localRoots[0].accessPoints[0].port = $port | .localRoots[0].accessPoints[0].address = $address' \
  "$DATA_DIR/topology.template.json" >"$DOWNSTREAM_NODE_DIR/topology.json"

cp -f "$DATA_DIR/downstream-node/config.json" "$DOWNSTREAM_NODE_DIR/config.json"

# Pre-seed the Leios DB so downstream can resolve EBs that the recorded
# Praos chain announces / certifies. See prepare-node0.sh for details.
if [ -f "$CLUSTER_RUN/leios.db" ]; then
  cp -f "$CLUSTER_RUN/leios.db" "$DOWNSTREAM_NODE_DIR/leios.db"
fi
