#!/usr/bin/env bash

set -eo pipefail

TX_RATE=3600
TX_DURATION=1
TX_COUNT=$((TX_RATE * TX_DURATION))
SLOTS=1500

truncate -s 0 jobs-fragmentation.list

for trial in {1..20}
do
  echo "npm run cli -- --nodes 10000 --degree 20 --adversaries 0 --adversary-degree 20 --tx-size-min 1500 --tx-size-max 1500 --tx-count $TX_COUNT --tx-duration $TX_DURATION --slots $SLOTS --log-level debug --log-target pino/file | tail -n +5 | gzip -9c > fragmentation-$trial.jsonl.gz" >> jobs-fragmentation.list
done

parallel --jobs=$(($(grep '^processor' /proc/cpuinfo | wc -l) * 1 / 2)) < jobs-fragmentation.list
