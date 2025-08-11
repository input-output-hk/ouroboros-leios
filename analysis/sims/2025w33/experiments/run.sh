#!/usr/bin/env nix-shell
#!nix-shell -i bash -p ansifilter gnugrep gnused gzip pigz bc

set -eo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

TX_START=0
TX_STOP=1200
SIM_STOP=1200
BW=50
CPU_COUNT=4
NETWORK=topology-v2
SIM=Rust
VARIANT=linear-with-tx-references
BLOCK_SIZE=10
TX_SIZE=1500
THROUGHPUT=0.150
LABEL=$(basename "$PWD")
PROPAGATION=$(echo "$LABEL" | sed -e 's/\(.*\),\(.*\),\(.*\),\(.*\),\(.*\)$/\1/')
STAGE_LENGTH_DIFF=$(echo "$LABEL" | sed -e 's/\(.*\),\(.*\),\(.*\),\(.*\),\(.*\)$/\2/')
STAGE_LENGTH_VOTE=$(echo "$LABEL" | sed -e 's/\(.*\),\(.*\),\(.*\),\(.*\),\(.*\)$/\3/')
EB_DELAY=$(echo "$LABEL" | sed -e 's/\(.*\),\(.*\),\(.*\),\(.*\),\(.*\)$/\4/')
TX_ATTACK=$(echo "$LABEL" | sed -e 's/\(.*\),\(.*\),\(.*\),\(.*\),\(.*\)$/\5/')
if [[ "$TX_ATTACK" == 0 ]]
then
  TX_SPACING_HONEST=$(echo "scale=3; $TX_SIZE / $THROUGHPUT / 1000" | bc)
  TX_SPACING_ADVERSARY=0
else
  TX_SPACING_HONEST=$(echo "scale=3; $TX_SIZE / $THROUGHPUT / 665" | bc)
  TX_SPACING_ADVERSARY=$(echo "scale=3; $TX_SIZE / $THROUGHPUT / 3" | bc)
fi
####TX_SPACING_HONEST=9999999999

ulimit -S -m 48000000 -v 48000000

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
, "late-eb-attack": {
    "attackers":{"nodes":["node-48","node-49","node-50","node-531","node-486","node-529","node-525","node-526","node-487","node-475","node-476","node-98","node-519","node-520","node-485","node-12","node-18","node-497","node-498","node-527","node-528","node-414","node-415","node-60","node-61","node-91","node-92","node-93","node-94","node-95","node-96","node-97","node-57","node-58","node-59","node-215","node-599","node-604","node-99","node-100","node-582","node-583","node-584","node-585","node-530","node-532","node-416","node-499","node-500","node-566","node-567","node-568","node-101","node-569","node-570","node-571","node-572","node-573","node-13"]}
  , "propagation-delay-ms": '"$EB_DELAY"'
  }
, "late-tx-attack": {
    "attackers":{"nodes":["node-48","node-49","node-50","node-531","node-486","node-529","node-525","node-526","node-487","node-475","node-476","node-98","node-519","node-520","node-485","node-12","node-18","node-497","node-498","node-527","node-528","node-414","node-415","node-60","node-61","node-91","node-92","node-93","node-94","node-95","node-96","node-97","node-57","node-58","node-59","node-215","node-599","node-604","node-99","node-100","node-582","node-583","node-584","node-585","node-530","node-532","node-416","node-499","node-500","node-566","node-567","node-568","node-101","node-569","node-570","node-571","node-572","node-573","node-13"]}
  , "attack-probability": '"$TX_ATTACK"'
  , "tx-generation-distribution": {distribution: "constant", value: '"$TX_SPACING_ADVERSARY"'}
  }
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

case "$SIM" in
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
Simulator,Variant,Network,Bandwidth,CPU,Diffusion duration,Voting duration,Max EB size,Propagation,EB delay,Tx attack,Tx size,Throughput,Tx start [s],Tx stop [s],Sim stop [s]
$SIM,$VARIANT,$NETWORK,$BW Mb/s,$CPU_COUNT vCPU/node,$STAGE_LENGTH_DIFF slot/stage,$STAGE_LENGTH_VOTE slot/stage,$BLOCK_SIZE MB/EB,$TX_SIZE B/Tx,$EB_DELAY s/EB,$TX_ATTACK %,$THROUGHPUT TxMB/s,$TX_START,$TX_STOP,$SIM_STOP
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
