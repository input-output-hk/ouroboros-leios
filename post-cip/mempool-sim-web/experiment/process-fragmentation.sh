#!/usr/bin/env bash

set -eo pipefail

(

echo $'Trial\tTime [s]\tNode ID\tTxId'

for f in fragmentation-*.jsonl.gz
do
  zcat $f \
  | jq -r '
      select(.msg == "memory pool contents")
    | .node as $node
    | .clock as $clock
    | .mempool.[]
    | ["'$(echo $f | sed -e 's/^fragmentation-\(.*\)\.jsonl\.gz$/\1/')'", $clock, $node, .]
    | @tsv
    '
done

) | gzip -9c > fragmentation.tsv.gz

