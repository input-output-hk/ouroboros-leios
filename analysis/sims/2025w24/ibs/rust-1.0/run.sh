#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

mkfifo sim.log

grep -E -v '(Slot|No.*Generated|CpuTask|Sent|Lottery)' sim.log | xz -9c > sim.log.xz &

../../sim-cli --parameters config.yaml network.yaml --slots 300 --conformance-events sim.log > stdout 2> stderr

wait
rm sim.log

cat << EOI > case.csv
simulator,tps
rust,$(basename $PWD)
EOI

xzcat sim.log.xz \
| ../../leios-trace-processor \
  +RTS -N5 -RTS \
  --trace-file /dev/stdin \
  --lifecycle-file lifecycle.csv \
  --cpu-file cpus.csv \
  --resource-file resources.csv \
  --receipt-file receipts.csv
  
pigz -9vf {lifecycle,cpus,resources,receipts}.csv

cat case.csv
