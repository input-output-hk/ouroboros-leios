#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

CX="$(basename "$PWD")"
BW=100

ulimit -S -m 24000000 -v 24000000

mkfifo sim.log

sed -e '/^tx-conflict-fraction:/s/:.*$/: '"$CX"'/' ../../config.yaml > config.yaml

sed -e 's/"bandwidth-bytes-per-second":125000000/"bandwidth-bytes-per-second":'"$((125000 * BW))"'/g' \
  ../../../../../data/simulation/pseudo-mainnet/topology-v2.yaml \
  > network.yaml

function cleanup() {
  rm sim.log
  rm network.yaml
}
trap cleanup EXIT

grep -E -v '(Slot|No.*Generated|CpuTask|Lottery)' sim.log | pigz -p 3 -9c > sim.log.gz &

../../sim-cli --parameters config.yaml network.yaml --slots 900 --conformance-events sim.log > stdout 2> stderr

wait

cat << EOI > case.csv
Simulator,Conflict fraction
Rust,$CX
EOI

zcat sim.log.gz \
| ../../leios-trace-processor \
  +RTS -N5 -RTS \
  --trace-file /dev/stdin \
  --lifecycle-file lifecycle.csv \
  --cpu-file cpus.csv \
  --resource-file resources.csv \
  --receipt-file receipts.csv
  
pigz -p 3 -9f {lifecycle,cpus,resources,receipts}.csv

cat case.csv
