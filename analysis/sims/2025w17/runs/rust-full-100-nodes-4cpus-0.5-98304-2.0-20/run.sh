#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

../../sim-cli --parameters config.json network.yaml --slots 600 sim.log > stdout 2> stderr

for f in ../../queries/*.sh
do
  n=$(basename ${f%%.sh})
  $f sim.log $n.csv.gz
done
gzip -9f sim.log

echo "FINISHED: rust | 600 | full | 100-nodes-4cpus | 0.5 | 98304 | 2.0 | 20"
