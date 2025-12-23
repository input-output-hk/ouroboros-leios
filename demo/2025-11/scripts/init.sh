set -exo pipefail

echo "Initializing WORKING_DIR"
if [ ! -d "$WORKING_DIR" ]; then
  mkdir "$WORKING_DIR"
  echo "Working directory created: $WORKING_DIR"
fi

touch "$WORKING_DIR/.env"
VARS_TO_DEFAULT=(
  CARDANO_NODE
  IMMDB_SERVER
  SECONDS_UNTIL_REF_SLOT
  REF_SLOT
  DATA_DIR
  LEIOS_MANIFEST
  PYTHON3
  ANALYSE_PY
  PORT_UPSTREAM_NODE
  PORT_NODE0
  PORT_DOWNSTREAM_NODE
  IP_UPSTREAM_NODE
  IP_NODE0
  IP_DOWNSTREAM_NODE
  RATE_UP_TO_N0
  DELAY_UP_TO_N0
  RATE_N0_TO_UP
  DELAY_N0_TO_UP
  RATE_N0_TO_DOWN
  DELAY_N0_TO_DOWN
  RATE_DOWN_TO_N0
  DELAY_DOWN_TO_N0
  CLUSTER_RUN
)

for var in "${VARS_TO_DEFAULT[@]}"; do
  def_var="DEF_$var"
  val=${!var:-${!def_var}}
  echo "$var=$val" >>"$WORKING_DIR/.env"
done

{
  echo "UPSTREAM_NODE_DIR=$WORKING_DIR/upstream-node"
  echo "NODE0_DIR=$WORKING_DIR/node0"
  echo "DOWNSTREAM_NODE_DIR=$WORKING_DIR/downstream-node"
  now=$(date +%s)
  echo "ONSET_OF_REF_SLOT=$((now + SECONDS_UNTIL_REF_SLOT))"
} >>"$WORKING_DIR/.env"

set -a && source "$WORKING_DIR/.env" && set +a

if [ ! -d "$WORKING_DIR/genesis" ]; then
  echo "Copying genesis"
  cp -fr "$CLUSTER_RUN/genesis" "$WORKING_DIR/genesis"
  chmod -R +rw "$WORKING_DIR/genesis"
fi
