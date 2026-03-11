#!/usr/bin/env bash

set -eo pipefail

TX_RATE=3
TX_DURATION=1200
TX_COUNT=$((TX_RATE * TX_DURATION))
SLOTS=$((TX_DURATION + 120))

truncate -s 0 jobs.list

for ADVERSARIES in $(seq 0 5 500)
do
  echo "npm run cli -- --nodes 10000 --degree 20 --adversaries $ADVERSARIES --adversary-degree 20 --adversary-delay 0 --tx-size-min 1500 --tx-size-max 1500 --tx-count $TX_COUNT --tx-duration $TX_DURATION --slots $SLOTS --log-target pino/file | tail -n +5 | gzip -9c > adversaries-wo-delay-$ADVERSARIES.jsonl.gz" >> jobs-adversaries-wo-delay.list
done

parallel --jobs=$(($(grep '^processor' /proc/cpuinfo | wc -l) * 1 / 3)) < jobs-adversaries-wo-delay.list
