set -exuo pipefail
set -a && source "$WORKING_DIR/.env" && set +a

if [ -d "$UPSTREAM_NODE_DIR" ]; then
  echo "Removing old $UPSTREAM_NODE_DIR"
  rm -fr "$UPSTREAM_NODE_DIR"
fi

mkdir "$UPSTREAM_NODE_DIR"
echo "Working directory created for upstream-node: $UPSTREAM_NODE_DIR"

# Check if user provided a custom Leios DB
if [[ -v LEIOS_DB ]] && [[ -f "$LEIOS_DB" ]]; then
  echo "Using user-provided Leios DB: $LEIOS_DB"
  cp -f "$LEIOS_DB" "$UPSTREAM_NODE_DIR/leios.db"
else
  echo "Generating Leios DB and base schedule..."
  leiosdemo202510 generate \
    "$UPSTREAM_NODE_DIR/leios.db" \
    "$LEIOS_MANIFEST" \
    "$UPSTREAM_NODE_DIR/base-schedule.json"
fi

# Check if user provided a pre-generated base schedule
if [[ -v LEIOS_BASE_SCHEDULE ]] && [[ -f "$LEIOS_BASE_SCHEDULE" ]]; then
  echo "Using user-provided base schedule: $LEIOS_BASE_SCHEDULE"
  cp -f "$LEIOS_BASE_SCHEDULE" "$UPSTREAM_NODE_DIR/base-schedule.json"
fi

# Ensure base-schedule.json exists (generate if needed)
if [[ ! -f "$UPSTREAM_NODE_DIR/base-schedule.json" ]]; then
  echo "Generating base schedule..."
  leiosdemo202510 generate \
    "$UPSTREAM_NODE_DIR/leios.db" \
    "$LEIOS_MANIFEST" \
    "$UPSTREAM_NODE_DIR/base-schedule.json"
fi

# Check if user provided a fully-adjusted custom schedule (bypasses EB_RELEASE_OFFSET)
if [[ -v LEIOS_SCHEDULE ]] && [[ -f "$LEIOS_SCHEDULE" ]]; then
  echo "Using user-provided final schedule: $LEIOS_SCHEDULE"
  echo "Note: EB_RELEASE_OFFSET will be ignored since a final schedule was provided"
  cp -f "$LEIOS_SCHEDULE" "$UPSTREAM_NODE_DIR/schedule.json"
else
  # Generate final schedule by applying EB_RELEASE_OFFSET to base schedule
  echo "Creating adjusted schedule with release offset..."
  # EB_RELEASE_OFFSET is added to the base schedule times (preserves relative timing between EBs)
  EB_RELEASE_OFFSET="${EB_RELEASE_OFFSET:-128.9}"
  jq "map(.[0] += $EB_RELEASE_OFFSET)" "$UPSTREAM_NODE_DIR/base-schedule.json" >"$UPSTREAM_NODE_DIR/schedule.json"
  echo "Schedule generated with EB release offset: $EB_RELEASE_OFFSET seconds"
fi

cp -f "$DATA_DIR/upstream-node/config.json" "$UPSTREAM_NODE_DIR/config.json"
tar -xzf "$CLUSTER_RUN/immutable.tar.gz" -C "$UPSTREAM_NODE_DIR"
chmod -R +rw "$UPSTREAM_NODE_DIR"
