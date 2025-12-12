set -exuo pipefail
set -a && source "$WORKING_DIR/.env" && set +a

if [ -d "$UPSTREAM_NODE_DIR" ]; then
  echo "Removing old $UPSTREAM_NODE_DIR"
  rm -fr "$UPSTREAM_NODE_DIR"
fi

mkdir "$UPSTREAM_NODE_DIR"
echo "Working directory created for upstream-node: $UPSTREAM_NODE_DIR"

echo "Generate the Leios DB and the schedules"

leiosdemo202510 generate \
  "$UPSTREAM_NODE_DIR/leios.db" \
  "$LEIOS_MANIFEST" \
  "$UPSTREAM_NODE_DIR/base-schedule.json"

if [[ ! -v LEIOS_SCHEDULE ]]; then
  jq 'map(.[0] = 182.9)' "$UPSTREAM_NODE_DIR/base-schedule.json" >"$UPSTREAM_NODE_DIR/schedule.json"
  echo "LEIOS_SCHEDULE not set, using default"
else
  cp -f "$LEIOS_SCHEDULE" "$UPSTREAM_NODE_DIR/schedule.json"
fi

cp -f "$DATA_DIR/upstream-node/config.json" "$UPSTREAM_NODE_DIR/config.json"
tar -xzf "$DATA_DIR/upstream-node/immutable.tar.gz" -C "$UPSTREAM_NODE_DIR"
chmod -R +rw "$UPSTREAM_NODE_DIR"
