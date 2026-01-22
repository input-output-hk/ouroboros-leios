#!/usr/bin/env bash

set -eo pipefail

truncate -s 0 jobs.list

for a in $(seq 0 5 500)
do
  echo "npm run cli -- --nodes 100 --degree 20 --adversaries 36 --adversary-degree 20 --tx-size-min 1500 --tx-size-max 1500 --tx-count 1800 --tx-duration 600 --slots 660 --log-target pino/file | tail -n +5 | gzip -9c > a=$a.jsonl.gz" >> jobs.list
done
