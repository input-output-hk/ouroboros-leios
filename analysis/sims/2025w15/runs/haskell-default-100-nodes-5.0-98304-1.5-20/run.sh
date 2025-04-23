#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

../../ols sim short-leios --leios-config-file config.json --topology-file network.yaml --shared-log-format --output-file sim.log --output-seconds 600 > stdout 2> stderr

for f in rbgen ebgen ibgen cpus receipts
do
  ../../queries/haskell/$f.sh sim.log $f.csv.gz
done
gzip -9f sim.log

echo "FINISHED: haskell | 600 | default | 100-nodes | 5.0 | 98304 | 1.5 | 20"
