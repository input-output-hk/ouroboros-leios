#!/usr/bin/env bash

set -e

cd "$(dirname "${BASH_SOURCE[0]}")"

../../ols sim short-leios --leios-config-file config.json --topology-file network.yaml --shared-log-format JSON --output-file sim.log --output-seconds 600 > stdout 2> stderr

for f in ../../queries/*.sh
do
  n=$(basename ${f%%.sh})
  $f sim.log $n.csv.gz
done
gzip -9f sim.log

echo "FINISHED: haskell | 600 | full | 100-nodes-4cpus | 1.0 | 98304 | 2.0 | 5"
