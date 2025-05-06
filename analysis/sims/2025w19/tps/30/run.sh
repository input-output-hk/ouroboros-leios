#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

../../sim-cli --parameters config.yaml network.yaml --slots 600 sim.log > stdout 2> stderr

gzip -9f sim.log

cat << EOI > case.csv
simulator,tps
rust,$(basename $PWD)
EOI

cat case.csv
