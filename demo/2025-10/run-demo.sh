set -e

echo "Setup a temporary working directory leios-run-tmp-dir"
rm -fr ./leios-run-tmp-dir || true
TMP_DIR=$(mktemp -d "${TMPDIR:-/tmp}"/leios-october-demo.XXXXXX)
ln -s "$TMP_DIR" ./leios-run-tmp-dir

echo "Generate the Leios DB and the schedules"
leiosdemo202510 generate "$TMP_DIR/upstream.db" manifest.json "$TMP_DIR/base-schedule.json"
# Make a schedule.json from the base-schedule.json such that the first number in each array is 182.9
jq 'map(.[0] = 182.9)' "$TMP_DIR/base-schedule.json" >"$TMP_DIR/schedule.json"

if [[ ! "$SECONDS_UNTIL_REF_SLOT" =~ ^[0-9]*$ ]] || [[ "$SECONDS_UNTIL_REF_SLOT" -le 0 ]]; then
  echo "Error: \${SECONDS_UNTIL_REF_SLOT} must be a positive integer of seconds, which will be added to the execution time of this script." >&2
  exit 1
fi

if [ ! -d "${DATA%/}" ]; then
  DATA="${DATA%/}"
  echo "Error: DATA directory '$DATA' not found or is not a directory." >&2
  exit 1
fi

if [[ -z "${CARDANO_NODE}" ]]; then
  echo "Error: \${CARDANO_NODE} must be the path to the cardano-node exe." >&2
  exit 1
fi

if [[ -z "${IMMDB_SERVER}" ]]; then
  echo "Error: \${IMMDB_SERVER} must be the path to the immdb-server exe." >&2
  exit 1
fi

if [[ -z "${REF_SLOT}" ]] || [[ ! "$REF_SLOT" =~ ^[0-9]*$ ]] || [[ "$REF_SLOT" -lt 0 ]]; then
  echo "Error: \${REF_SLOT} must be a non-negative integer, a slot number" >&2
  exit 1
fi

now=$(date +%s)
ONSET_OF_REF_SLOT=$((now + SECONDS_UNTIL_REF_SLOT))
echo "REF_SLOT=$REF_SLOT"
echo "ONSET_OF_REF_SLOT=$ONSET_OF_REF_SLOT"
echo "$REF_SLOT"
echo "$ONSET_OF_REF_SLOT"

# arbitrary choices

PORT1=3001
PORT2=3002
PORT3=3003

TOXIPROXY=100

if pgrep -fx "toxiproxy-server" >/dev/null; then
  echo "Toxiproxy is already running"
else
  echo "Starting Toxiproxy"
  toxiproxy-server 1>"$TMP_DIR/toxiproxy.log" 2>&1 &
fi

# shellcheck disable=SC2329
cleanup_proxy() {
  toxiproxy-cli delete mocked-upstream-peer-proxy 2>/dev/null || true
  toxiproxy-cli delete node0-proxy 2>/dev/null || true
}

trap cleanup_proxy EXIT INT TERM

# Clean up any existing proxies from previous runs
cleanup_proxy

toxiproxy-cli create --listen 127.0.0.1:"$PORT1" --upstream 127.0.0.1:"$((TOXIPROXY + PORT1))" mocked-upstream-peer-proxy
toxiproxy-cli create --listen 127.0.0.1:"$PORT2" --upstream 127.0.0.1:"$((TOXIPROXY + PORT2))" node0-proxy

for i in mocked-upstream-peer-proxy node0-proxy; do
  # TODO magic numbers
  toxiproxy-cli toxic add --type latency --attribute latency=150 --attribute jitter=30 $i # milliseconds
  toxiproxy-cli toxic add --type bandwidth --attribute rate=2500 $i                       # kilobytes per second
  # FYI, 125 kilobyte/s = 1 megabit/s, so EG 2500 kilobyte/s = 20 megabit/s
done

echo "Ports: ${PORT1} ${PORT2} ${PORT3}, each plus ${TOXIPROXY} for toxiproxy"

##
## Run cardano-node (node-0)
##

echo "Creating $TMP_DIR/topology-node-0.json"
cat <<EOF >"$TMP_DIR/topology-node-0.json"
{
  "bootstrapPeers": [],
  "localRoots": [
    {
      "accessPoints": [
        {
          "address": "127.0.0.1",
          "port": ${PORT1}
        }
      ],
      "advertise": false,
      "trustable": true,
      "valency": 1
    }
  ],
  "publicRoots": []
}
EOF

mkdir -p "$TMP_DIR/node-0/db"
cat leios-schema.sql | sqlite3 "$TMP_DIR/node-0/leios.db"

env LEIOS_DB_PATH="$TMP_DIR/node-0/leios.db" \
  "$CARDANO_NODE" run \
  --config "$DATA/leios-node/config.json" \
  --topology "$TMP_DIR/topology-node-0.json" \
  --database-path "$TMP_DIR/node-0/db" \
  --socket-path "$TMP_DIR/node-0.socket" \
  --host-addr 127.0.0.1 --port $((TOXIPROXY + PORT2)) \
  &>"$TMP_DIR/cardano-node-0.log" &

CARDANO_NODE_0_PID=$!

echo "Cardano node 0 started with PID: $CARDANO_NODE_0_PID"

##
## Run a second Cardano-node (To be eventually replaced by a mocked downstream node)
##

cat <<EOF >"$TMP_DIR/topology-node-1.json"
{
  "bootstrapPeers": [],
  "localRoots": [
    {
      "accessPoints": [
        {
          "address": "127.0.0.1",
          "port": ${PORT2}
        }
      ],
      "advertise": false,
      "trustable": true,
      "valency": 1
    }
  ],
  "publicRoots": []
}
EOF

mkdir -p "$TMP_DIR/node-1/db"
cat leios-schema.sql | sqlite3 "$TMP_DIR/node-1/leios.db"

env LEIOS_DB_PATH="$TMP_DIR/node-1/leios.db" \
  "$CARDANO_NODE" run \
  --config "$DATA/leios-node/config.json" \
  --topology "$TMP_DIR/topology-node-1.json" \
  --database-path "$TMP_DIR/node-1/db" \
  --socket-path "$TMP_DIR/node-1.socket" \
  --host-addr 127.0.0.1 --port "$PORT3" \
  &>"$TMP_DIR/cardano-node-1.log" &

MOCKED_PEER_PID=$!

echo "Cardano node 1 started with PID: $MOCKED_PEER_PID"

##
## Run immdb-server
##

"$IMMDB_SERVER" \
  --db "$DATA/immdb-node/immutable/" \
  --config "$DATA/immdb-node/config.json" \
  --initial-slot "$REF_SLOT" \
  --initial-time "$ONSET_OF_REF_SLOT" \
  --leios-schedule "$TMP_DIR/schedule.json" \
  --leios-db "$TMP_DIR/upstream.db" \
  --port $((TOXIPROXY + PORT1)) \
  &>"$TMP_DIR/immdb-server.log" &

IMMDB_SERVER_PID=$!

echo "ImmDB server started with PID: $IMMDB_SERVER_PID"

# Wait briefly and check if immdb-server is still running
sleep 2
if ! kill -0 "$IMMDB_SERVER_PID" 2>/dev/null; then
  echo "ERROR: ImmDB server (PID $IMMDB_SERVER_PID) failed to start" >&2
  echo "Log output from $TMP_DIR/immdb-server.log:" >&2
  cat "$TMP_DIR/immdb-server.log" >&2
  kill "$CARDANO_NODE_0_PID" "$MOCKED_PEER_PID" 2>/dev/null || true
  exit 1
fi

echo "All processes running successfully"

TIMEOUT=25
read -t $TIMEOUT -n 1 -s -r -p "Press any key to stop the spawned processes, or just wait $TIMEOUT seconds..." || true
echo

echo "Killing processes $IMMDB_SERVER_PID (immdb-server), $CARDANO_NODE_0_PID (node-0), and $MOCKED_PEER_PID (node-1)..."

kill "$IMMDB_SERVER_PID" 2>/dev/null || true
# Use negative PID to target the process group ID and SIGKILL for cardano-node processes.
kill "$CARDANO_NODE_0_PID" 2>/dev/null || true
kill "$MOCKED_PEER_PID" 2>/dev/null || true

echo "Temporary data stored at: $TMP_DIR"

# Database dumps

echo
echo "=== Database Dumps ==="
echo

echo "--- ImmDB Server (immutable db) ---"
db-analyser --db "$DATA/immdb-node/" --show-slot-block-no --v2-in-mem cardano --config "$DATA/immdb-node/config.json" >"$TMP_DIR/immdb-server-db-dump.txt" 2>&1
echo "Saved to: $TMP_DIR/immdb-server-db-dump.txt"
echo

echo "--- Node 0 (immutable db) ---"
if [ -d "$TMP_DIR/node-0/db/immutable" ]; then
  db-analyser --db "$TMP_DIR/node-0/db/" --show-slot-block-no --v2-in-mem cardano --config "$DATA/leios-node/config.json" >"$TMP_DIR/node-0-db-dump.txt" 2>&1
  echo "Saved to: $TMP_DIR/node-0-db-dump.txt"
else
  echo "No immutable db found at $TMP_DIR/node-0/db/immutable/"
fi
echo

echo "--- Node 1 (immutable db) ---"
if [ -d "$TMP_DIR/node-1/db/immutable" ]; then
  db-analyser --db "$TMP_DIR/node-1/db/" --show-slot-block-no --v2-in-mem cardano --config "$DATA/leios-node/config.json" >"$TMP_DIR/node-1-db-dump.txt" 2>&1
  echo "Saved to: $TMP_DIR/node-1-db-dump.txt"
else
  echo "No immutable db found at $TMP_DIR/node-1/db/immutable/"
fi
echo

echo "=== Leios SQLite Databases ==="
echo

echo "--- Upstream Leios DB ---"
sqlite3 "$TMP_DIR/upstream.db" ".dump" >"$TMP_DIR/upstream-leios-db-dump.sql"
echo "Saved to: $TMP_DIR/upstream-leios-db-dump.sql"
echo

echo "--- Node 0 Leios DB ---"
sqlite3 "$TMP_DIR/node-0/leios.db" ".dump" >"$TMP_DIR/node-0-leios-db-dump.sql"
echo "Saved to: $TMP_DIR/node-0-leios-db-dump.sql"
echo

echo "--- Node 1 Leios DB ---"
sqlite3 "$TMP_DIR/node-1/leios.db" ".dump" >"$TMP_DIR/node-1-leios-db-dump.sql"
echo "Saved to: $TMP_DIR/node-1-leios-db-dump.sql"
echo

# Log analysis

cat "$TMP_DIR/cardano-node-0.log" | grep -v -i -e leios >"$TMP_DIR/logA"
cat "$TMP_DIR/cardano-node-1.log" | grep -v -i -e leios >"$TMP_DIR/logB"

python3 analyse.py \
  "$REF_SLOT" "$ONSET_OF_REF_SLOT" \
  "$TMP_DIR/logA" "$TMP_DIR/logB" \
  "$TMP_DIR/scatter_plot.png"

# Status

echo
echo "Any processes still running:"
# shellcheck disable=SC2009
ps aux | grep -e '[c]ardano-node' -e '[i]mmdb' | cut -c-180

echo "(Hopefully there were none!)"

exit 0
