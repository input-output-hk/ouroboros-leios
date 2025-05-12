#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

../../sim-cli --parameters config.yaml network.yaml --slots 2400 sim.log > stdout 2> stderr

for f in ../../queries/*.sh
do
  n=$(basename ${f%%.sh})
  $f sim.log $n.csv.gz
done

gzip -9f sim.log

cat << EOI > case.csv
simulator,tps
rust,$(basename $PWD)
EOI

cat case.csv
