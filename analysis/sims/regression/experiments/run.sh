#!/usr/bin/env nix-shell
#!nix-shell -i bash -p ansifilter gnugrep gnused gzip pigz bc

set -eo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

BW=10
CPU_COUNT=4
NETWORK=topology-v2
SIM=$(basename "$PWD")

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

function cleanup() {
  rm sim.log
  rm network.yaml
}
trap cleanup EXIT

grep -E -v '(Slot|No.*Generated|CpuTask|Lottery)' sim.log | pigz -p 3 -9c > sim.log.gz &

../../sim-cli-$SIM --parameters ../config.yaml network.yaml --slots 1200 --conformance-events sim.log > stdout 2> stderr

wait

cat << EOI > case.csv
sim-cli,Tx start [s],Tx stop [s],Sim stop [s]
$SIM,60,960,1200
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

ansifilter stdout | grep -E '^ INFO (praos|leios|network): ' > summary.txt
