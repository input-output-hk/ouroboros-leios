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

RUN_DIR="$RUNS_DIR/$ID"
mkdir -p "$RUN_DIR"

cat "$DIR/config.$LABEL.yaml" - << EOI | yaml2json > "$RUN_DIR/config.json"
ib-generation-probability: $IB_RATE
ib-body-avg-size-bytes: $IB_SIZE
ib-body-max-size-bytes: $IB_SIZE
eb-generation-probability: $EB_RATE
leios-stage-length-slots: $STAGE_LENGTH
leios-stage-active-voting-slots: $STAGE_LENGTH
EOI

ln -f -s "../../$NETWORK.yaml" "$RUN_DIR/network.yaml"

cat << EOI > "$RUN_DIR/case.csv"
simulator,label,network,ib-generation-probability,ib-body-avg-size-bytes,eb-generation-probability,leios-stage-length-slots
$SIMULATOR,$LABEL,$NETWORK,$IB_RATE,$IB_SIZE,$EB_RATE,$STAGE_LENGTH
EOI

cat << EOI > "$RUN_DIR/run.sh"
#!/usr/bin/env bash

set -e

cd "\$(dirname "\${BASH_SOURCE[0]}")"

EOI

case "$SIMULATOR" in
  haskell)
    echo "../../ols sim short-leios --leios-config-file config.json --topology-file network.yaml --shared-log-format --output-file sim.log --output-seconds $MAX_SLOT > stdout 2> stderr" >> "$RUN_DIR/run.sh"
  ;;
rust)
    echo "../../sim-cli --parameters config.json network.yaml --slots $MAX_SLOT sim.log > stdout 2> stderr" >> "$RUN_DIR/run.sh"
  ;;
esac

cat << EOI >> "$RUN_DIR/run.sh"

for f in rbgen ebgen ibgen cpus receipts
do
  ../../queries/$SIMULATOR/\$f.sh sim.log \$f.csv.gz
done
gzip -9f sim.log

echo "FINISHED: $SIMULATOR | $MAX_SLOT | $LABEL | $NETWORK | $IB_RATE | $IB_SIZE | $EB_RATE | $STAGE_LENGTH"
EOI

chmod +x "$RUN_DIR/run.sh"
