#!/usr/bin/env bash

DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

RUNS_DIR="$DIR/runs"

SIMULATOR="$1"
MAX_SLOT="$2"
LABEL="$3"
NETWORK="$4"
IB_RATE="$5"
IB_SIZE="$6"
EB_RATE="$7"
STAGE_LENGTH="$8"

ID="$SIMULATOR-$LABEL-$NETWORK-$IB_RATE-$IB_SIZE-$EB_RATE-$STAGE_LENGTH"

COLLECTION="RAW_$(echo $ID | md5sum | sed -e 's/^\(.\{8\}\).*/\1/')"

RUN_DIR="$RUNS_DIR/$ID"
mkdir -p "$RUN_DIR"

cat "$DIR/config.$LABEL.yaml" - << EOI | yaml2json > "$RUN_DIR/config.json"
ib-generation-probability: $IB_RATE
ib-body-avg-size-bytes: $IB_SIZE
ib-body-max-size-bytes: $IB_SIZE
eb-generation-probability: $EB_RATE
leios-stage-length-slots: $STAGE_LENGTH
EOI

ln -f -s "../../$NETWORK.yaml" "$RUN_DIR/network.yaml"

SCENARIO='{"label": "'"$LABEL"'", "network": "'"$NETWORK"'", "ib-generation-probability": '"$IB_RATE"', "ib-body-avg-size-bytes": '"$IB_SIZE"', "eb-generation-probability": '"$EB_RATE"', "leios-stage-length-slots": '"$STAGE_LENGTH"'}'

cat << EOI > "$RUN_DIR/scenario.js"
const scenario = $SCENARIO
const simulator = "$SIMULATOR"
const raw = "$COLLECTION"
EOI

cat << EOI > "$RUN_DIR/run.sh"
#!/usr/bin/env bash

set -ev

cd "\$(dirname "\${BASH_SOURCE[0]}")"

echo "SCENARIO: $SIMULATOR | $MAX_SLOT | $LABEL | $NETWORK | $IB_RATE | $IB_SIZE | $EB_RATE | $STAGE_LENGTH"

if [[ ! -p sim.log ]]
then
  mkfifo sim.log
fi

cleanup() {
  if [[ -p sim.log ]]
  then
    rm sim.log
  fi
}

trap cleanup EXIT

mongoimport --host "\$HOST" --db "\$DB" --collection "$COLLECTION" --drop sim.log &

EOI

case "$SIMULATOR" in
  haskell)
    echo "../../ols sim short-leios --leios-config-file config.json --topology-file network.yaml --output-file sim.log --output-seconds $MAX_SLOT > stdout 2> stderr" >> "$RUN_DIR/run.sh"
  ;;
rust)
    echo "../../sim-cli --parameters config.json network.yaml --slots $MAX_SLOT sim.log > stdout 2> stderr" >> "$RUN_DIR/run.sh"
  ;;
esac

cat << EOI >> "$RUN_DIR/run.sh"

echo "SCENARIO: $SIMULATOR | $MAX_SLOT | $LABEL | $NETWORK | $IB_RATE | $IB_SIZE | $EB_RATE | $STAGE_LENGTH"

mongo --host "\$HOST" "\$DB" scenario.js "../../queries/import.js"
EOI

chmod +x "$RUN_DIR/run.sh"
