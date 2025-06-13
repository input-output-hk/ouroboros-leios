#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

mkfifo sim.log

grep -E -v '(Slot|No.*Generated|CpuTask|Sent|Lottery)' sim.log | xz -9c > sim.log.xz &

../../ols sim leios --leios-config-file config.yaml --topology-file network.yaml --shared-log-format JSON --conformance-events --output-file sim.log --output-seconds 300 > stdout 2> stderr

wait
rm sim.log

cat << EOI > case.csv
simulator,tps
rust,$(basename $PWD)
EOI

xzcat sim.log.xz \
| ../../leios-trace-processor \
  --trace-file /dev/stdin \
  --lifecycle-file lifecycle.csv \
  --cpu-file cpus.csv \
  --resource-file resources.csv \
  --receipt-file receipts.csv
  
pigz -9vf {lifecycle,cpus,resources,receipts}.csv

cat case.csv
