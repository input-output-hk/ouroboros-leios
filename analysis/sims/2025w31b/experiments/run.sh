#!/usr/bin/env nix-shell
#!nix-shell -i bash -p ansifilter gnugrep gnused gzip pigz bc

set -eo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

TX_SIZE=0
TX_START=0
TX_STOP=1200
SIM_STOP=1200
BW=50
EB_RATE=2.5
NETWORK=topo-default-100
LABEL=$(basename "$PWD")
SIM="$LABEL"
VARIANT=linear
STAGE_LENGTH=8
BLOCK_SIZE=10
THROUGHPUT=0.150

ulimit -S -m 48000000 -v 48000000

if [[ -e sim.log ]]
then
  rm sim.log
fi

mkfifo sim.log

sed -e 's/"bandwidth-bytes-per-second":125000000/"bandwidth-bytes-per-second":'"$((125000 * BW))"'/g' \
  "../../../../../data/simulation/$NETWORK.yaml" \
  > network.yaml

yaml2json ../config.yaml \
| jq '. + 
{
  "leios-variant": "'"$VARIANT"'"
, "linear-vote-stage-length-slots": '"$STAGE_LENGTH"'
, "linear-diffuse-stage-length-slots": '"$STAGE_LENGTH"'
, "leios-stage-length-slots": '"$STAGE_LENGTH"'
, "eb-referenced-txs-max-size-bytes": ('"$BLOCK_SIZE"' * 1000000)
, "eb-body-avg-size-bytes": ('"$BLOCK_SIZE"' * 1000000)
, "eb-generation-probability": '"$EB_RATE"'
, "tx-size-bytes-distribution": {distribution: "constant", value: '"$TX_SIZE"'}
, "tx-generation-distribution": {distribution: "constant", value: ('"$TX_SIZE"' / '"$THROUGHPUT"' / 1000)}
, "tx-start-time": '"$TX_START"'
, "tx-stop-time": '"$TX_STOP"'
}
' > config.yaml

function cleanup() {
  rm sim.log
  rm network.yaml
}
trap cleanup EXIT

grep -E -v '(Slot|No.*Generated|CpuTask|Lottery)' sim.log | pigz -p 3 -9c > sim.log.gz &

case "$LABEL" in
  Rust)
    ../../sim-cli --parameters config.yaml network.yaml --slots "$SIM_STOP" --conformance-events sim.log > stdout 2> stderr
    ;;
  Haskell)
    ../../ols sim leios --leios-config-file config.yaml --topology-file network.yaml --shared-log-format JSON --conformance-events --output-file sim.log --output-seconds "$SIM_STOP" > stdout 2> stderr
    ;;
  *)
    false
esac

wait

cat << EOI > case.csv
Simulator,Variant,Network,Bandwidth,Stage length,EB rate,Max EB size,Tx size,Throughput,Tx start [s],Tx stop [s],Sim stop [s]
$SIM,$VARIANT,$NETWORK,$BW Mb/s,$STAGE_LENGTH slot/stage,$EB_RATE EB/stage,$BLOCK_SIZE MB/EB,$TX_SIZE B/Tx,$THROUGHPUT TxMB/s,$TX_START,$TX_STOP,$SIM_STOP
EOI

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
  
pigz -p 3 -9f {cpus,lifecycle,receipts,resources,sizes}.csv

cat case.csv

if [[ "$SIM" == "Rust" ]]
then
  ansifilter stdout | grep -E '^ INFO (praos|leios|network): ' > summary.txt
fi
