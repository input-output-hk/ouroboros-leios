#!/usr/bin/env bash

set -euo pipefail
shopt -s nullglob

TX_RATE=3
TX_DURATION=1200
TX_SIZE=1500
TX_LOAD=$(((TX_RATE * TX_SIZE + 500) / 1000)) # rounded KB/s
SLOTS=$((TX_DURATION + 120))

JOB_FILE=jobs-adversaries.list

rm -f adversaries-[0-9]*.jsonl.gz
: > "$JOB_FILE"

for ADVERSARIES in $(seq 0 5 500)
do
  echo "npm run cli -- --nodes 10000 --degree 20 --adversaries $ADVERSARIES --adversary-degree 20 --tx-size $TX_SIZE --tx-load $TX_LOAD --tx-duration $TX_DURATION --slots $SLOTS --log-target pino/file | tail -n +5 | gzip -9c > adversaries-$ADVERSARIES.jsonl.gz" >> "$JOB_FILE"
done

if command -v nproc >/dev/null 2>&1
then
  CPU_COUNT=$(nproc)
else
  CPU_COUNT=$(sysctl -n hw.ncpu)
fi
JOBS=$((CPU_COUNT / 2))
if [ "$JOBS" -lt 1 ]
then
  JOBS=1
fi

parallel --jobs="$JOBS" < "$JOB_FILE"
