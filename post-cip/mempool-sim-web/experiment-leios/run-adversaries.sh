#!/usr/bin/env bash

set -eo pipefail

TX_DURATION=300
TX_SIZE=1500
TX_RATE=6
TX_COUNT=$((TX_RATE * TX_DURATION))
TX_LOAD=$((TX_RATE * TX_SIZE / 1000))
SLOTS=$((TX_DURATION + 60))

truncate -s 0 jobs-adversaries.list

for ADVERSARIES in $(seq 0 5 500)
do
  echo "npm run cli -- --nodes 10000 --degree 20 --eb --adversaries $ADVERSARIES --adversary-degree 20 --tx-size $TX_SIZE --tx-load $TX_LOAD --tx-duration $TX_DURATION --slots $SLOTS --log-target pino/file | tail -n +5 | gzip -9c > adversaries-$ADVERSARIES.jsonl.gz" >> jobs-adversaries.list
done

parallel --jobs=$(($(grep '^processor' /proc/cpuinfo | wc -l) * 1 / 2)) < jobs-adversaries.list
