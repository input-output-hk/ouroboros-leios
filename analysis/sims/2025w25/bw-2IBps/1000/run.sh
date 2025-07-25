#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

BW=$(basename $PWD)

ulimit -S -m 24000000 -v 24000000

mkfifo sim.log

sed -e 's/"bandwidth-bytes-per-second":125000000/"bandwidth-bytes-per-second":'"$((125000 * BW))"'/g' \
  ../../../../../data/simulation/pseudo-mainnet/topology-v2.yaml \
  > network.yaml

function cleanup() {
  rm sim.log
  rm network.yaml
}
trap cleanup EXIT

grep -E -v '(Slot|No.*Generated|CpuTask|Lottery)' sim.log | pigz -p 3 -9c > sim.log.gz &

../../sim-cli --parameters config.yaml network.yaml --slots 1200 --conformance-events sim.log > stdout 2> stderr

wait

cat << EOI > case.csv
Simulator,Bandwidth [Mb/s]
Rust,$(basename $PWD)
EOI

zcat sim.log.gz \
| ../../leios-trace-processor \
  +RTS -N5 -RTS \
  --trace-file /dev/stdin \
  --lifecycle-file lifecycle.csv \
  --cpu-file cpus.csv \
  --resource-file resources.csv \
  --receipt-file receipts.csv
  
pigz -p 3 -9vf {lifecycle,cpus,resources,receipts}.csv

cat case.csv
