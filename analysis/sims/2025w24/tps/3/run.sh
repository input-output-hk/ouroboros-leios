#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

mkfifo sim.log

grep -E -v '(Slot|No.*Generated|CpuTask|Sent|Lottery)' sim.log | xz -9c > sim.log.xz &

../../sim-cli --parameters config.yaml network.yaml --slots 840 --conformance-events sim.log > stdout 2> stderr

wait
rm sim.log

cat << EOI > case.csv
simulator,tps
rust,$(basename $PWD)
EOI

cat case.csv
