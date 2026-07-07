set -exuo pipefail

if [ -d "$UPSTREAM_NODE_DIR" ]; then
  echo "Removing old $UPSTREAM_NODE_DIR"
  rm -fr "$UPSTREAM_NODE_DIR"
fi

mkdir "$UPSTREAM_NODE_DIR"
echo "Working directory created for upstream-node: $UPSTREAM_NODE_DIR"

echo "Generate the Leios DB and the schedules"

leios-schedule-gen \
  "$UPSTREAM_NODE_DIR/leios.db" \
  "$LEIOS_MANIFEST" \
  "$UPSTREAM_NODE_DIR/base-schedule.json"

if [[ ! -v LEIOS_SCHEDULE ]]; then
  : "${BURST_SLOT:=219.9}"
  jq "map(.[0] = $BURST_SLOT)" "$UPSTREAM_NODE_DIR/base-schedule.json" >"$UPSTREAM_NODE_DIR/schedule.json"
  echo "LEIOS_SCHEDULE not set, bursting all EBs at slot $BURST_SLOT"
else
  cp -f "$LEIOS_SCHEDULE" "$UPSTREAM_NODE_DIR/schedule.json"
fi

cp -f "$DATA_DIR/upstream-node/config.json" "$UPSTREAM_NODE_DIR/config.json"
tar -xzf "$CLUSTER_RUN/immutable.tar.gz" -C "$UPSTREAM_NODE_DIR"
chmod -R +rw "$UPSTREAM_NODE_DIR"
