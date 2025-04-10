#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

../../sim-cli --parameters config.json network.yaml --slots 600 sim.log > stdout 2> stderr

for f in rbgen ebgen ibgen cpus receipts
do
  ../../queries/rust/$f.sh sim.log $f.csv.gz
done
gzip -9f sim.log

echo "FINISHED: rust | 600 | default | 100-nodes | 9.5 | 98304 | 1.5 | 20"
