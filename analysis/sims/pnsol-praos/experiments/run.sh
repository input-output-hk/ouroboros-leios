#!/usr/bin/env nix-shell
#!nix-shell -i bash -p ansifilter gnugrep gnused gzip pigz bc

set -eo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

TX_START=0
TX_STOP=1200
SIM_STOP=1200
BW=10
CPU_COUNT=4
NETWORK=topology-v2
SIM=Rust
VARIANT=linear-with-tx-references
BLOCK_SIZE=0
TX_SIZE=1500
LABEL=$(basename "$PWD")
PROPAGATION=eb-received
STAGE_LENGTH_DIFF=1200
STAGE_LENGTH_VOTE=1200
PLUTUS=$(echo -n "$LABEL" | sed -e 's/^\(.*\),\(.*\)/\1/')
THROUGHPUT=$(echo -n "$LABEL" | sed -e 's/^\(.*\),\(.*\)/\2/')
TX_SPACING_HONEST=$(echo "scale=3; $TX_SIZE / $THROUGHPUT / 1000" | bc)

ulimit -S -m 128000000 -v 128000000

if [[ -e sim.log ]]
then
  rm sim.log
fi

mkfifo sim.log

sed -e 's/"bandwidth-bytes-per-second":125000000/"bandwidth-bytes-per-second":'"$((125000 * BW))"'/g' \
    -e 's/"cpu-core-count":6,/"cpu-core-count":'"$CPU_COUNT"',/g' \
    "../../../../../data/simulation/pseudo-mainnet/$NETWORK.yaml" \
  > network.yaml

yaml2json ../config.yaml \
| jq '. + 
{
  "leios-variant": "'"$VARIANT"'"
, "linear-eb-propagation-criteria": "'"$PROPAGATION"'"
, "linear-diffuse-stage-length-slots": '"$STAGE_LENGTH_DIFF"'
, "linear-vote-stage-length-slots": '"$STAGE_LENGTH_VOTE"'
, "leios-stage-length-slots": '"$STAGE_LENGTH_VOTE"'
, "eb-referenced-txs-max-size-bytes": ('"$BLOCK_SIZE"' * 1000000)
, "eb-body-avg-size-bytes": ('"$BLOCK_SIZE"' * 1000000)
, "tx-size-bytes-distribution": {distribution: "constant", value: '"$TX_SIZE"'}
, "tx-generation-distribution": {distribution: "constant", value: '"$TX_SPACING_HONEST"'}
, "tx-start-time": '"$TX_START"'
, "tx-stop-time": '"$TX_STOP"'
} + (
  if "'"$PLUTUS"'" == "NA"
  then
    {}
  else
    {
      "tx-validation-cpu-time-ms": (0.2624 + ("'"$PLUTUS"'" | tonumber) * 0.05 / '"$THROUGHPUT"' / 1000000 * '"$TX_SIZE"' * 0.9487)
    , "rb-body-legacy-praos-payload-validation-cpu-time-ms-constant": (0.3478 + 20 * 0.02127)
    , "rb-body-legacy-praos-payload-validation-cpu-time-ms-per-byte": 0.00001943
    , "eb-body-validation-cpu-time-ms-constant": (0.3478 + (("'"$PLUTUS"'" | tonumber) - 20) * 0.02127)
    , "eb-body-validation-cpu-time-ms-per-byte": 0.00001943
    }
  end
)
' > config.yaml

function cleanup() {
  rm sim.log
  rm network.yaml
}
trap cleanup EXIT

grep -E -v '(Slot|CpuTask|Lottery)' sim.log | pigz -p 3 -9c > sim.log.gz &

case "$SIM" in
  Rust)
    export RUST_BACKTRACE=1
    ../../sim-cli --parameters config.yaml network.yaml --slots "$SIM_STOP" --conformance-events sim.log > stdout 2> stderr
    ;;
  Haskell)
    ../../ols sim leios --leios-config-file config.yaml --topology-file network.yaml --shared-log-format JSON --conformance-events --output-file sim.log --output-seconds "$SIM_STOP" > stdout 2> stderr
    ;;
  *)
    false
esac

wait

if [[ "$PLUTUS" == "NA" ]]
then
cat << EOI > case.csv
Network,Bandwidth,CPU,Diffusion duration,Voting duration,Max EB size,Tx size,Throughput,Plutus,Tx start [s],Tx stop [s],Sim stop [s]
$NETWORK,$BW Mb/s,$CPU_COUNT vCPU/node,L_diff = $STAGE_LENGTH_DIFF slots,L_vote = $STAGE_LENGTH_VOTE slots,$BLOCK_SIZE MB/EB,$TX_SIZE B/Tx,$THROUGHPUT TxMB/s,,$TX_START,$TX_STOP,$SIM_STOP
EOI
else
cat << EOI > case.csv
Network,Bandwidth,CPU,Diffusion duration,Voting duration,Max EB size,Tx size,Throughput,Plutus,Tx start [s],Tx stop [s],Sim stop [s]
$NETWORK,$BW Mb/s,$CPU_COUNT vCPU/node,L_diff = $STAGE_LENGTH_DIFF slots,L_vote = $STAGE_LENGTH_VOTE slots,$BLOCK_SIZE MB/EB,$TX_SIZE B/Tx,$THROUGHPUT TxMB/s,$PLUTUS Gstep/EB,$TX_START,$TX_STOP,$SIM_STOP
EOI
fi

zcat sim.log.gz \
| ../../leios-trace-processor \
  +RTS -N5 -RTS \
  --trace-file /dev/stdin \
  --lifecycle-file lifecycle.csv \
  --cpu-file cpus.csv \
  --resource-file resources.csv \
  --receipt-file receipts.csv

(
  echo 'Kind,Item,Generated [s],Transactions,Endorses'
  zcat sim.log.gz \
  | grep -E '(EB|RB)Generated' \
  | jq -r '
    .message.type[0:2]
    + "," + .message.id
    + "," + (.time_s | tostring)
    + "," + (.message.transactions | length | tostring)
    + "," + (if .message.endorsement then .message.endorsement.eb.id else "NA" end)
  '
) > sizes.csv

../../postprocessing.sh

pigz -p 3 -9f {cpus,lifecycle,receipts,resources,sizes}.csv

cat case.csv

if [[ "$SIM" == "Rust" ]]
then
  ansifilter stdout | grep -E '^ INFO (praos|leios|network): ' > summary.txt
fi
