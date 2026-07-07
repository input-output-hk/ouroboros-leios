set -exuo pipefail

if [ -d "$NODE0_DIR" ]; then
  echo "Removing old $NODE0_DIR"
  rm -fr "$NODE0_DIR"
fi

mkdir "$NODE0_DIR"
echo "Working directory created for node0: $NODE0_DIR"

jq \
  --argjson port "$PORT_UPSTREAM_NODE" \
  --arg address "$IP_UPSTREAM_NODE" \
  '.localRoots[0].accessPoints[0].port = $port | .localRoots[0].accessPoints[0].address = $address' \
  "$DATA_DIR/topology.template.json" >"$NODE0_DIR/topology.json"

cp -f "$DATA_DIR/node0/config.json" "$NODE0_DIR/config.json"

# Pre-seed the Leios DB so node0 can resolve EBs that the recorded
# Praos chain announces / certifies. Otherwise the ledger panics at
# Ledger.hs:1002 the moment it applies a cert block whose EB body
# hasn't yet been LeiosFetched.
if [ -f "$CLUSTER_RUN/leios.db" ]; then
  cp -f "$CLUSTER_RUN/leios.db" "$NODE0_DIR/leios.db"
fi
