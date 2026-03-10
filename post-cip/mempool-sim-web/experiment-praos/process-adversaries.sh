#!/usr/bin/env bash

set -eo pipefail

(

echo $'Adversarial nodes\tRB ID\tRB honest txs\tRB adversarial txs\tEB ID\tEB honest txs\tEB adversarial txs'
for f in $(find -cnewer jobs-adversaries.list -size +1 -name adversaries-\*.jsonl.gz)
do
  zcat $f \
| jq -rs '
    .[0].adversaries as $adversaries
  | .[]
  | select(.msg == "block produced")
  | [
      $adversaries
    , .blockId
    , .honestCount
    , .adversarialCount
    , .certifiedEB.ebId // ""
    , .certifiedEB.honestCount // 0
    , .certifiedEB.adversarialCount // 0
    ]
  | @tsv
'
done

) | gzip -9c > adversaries.tsv.gz
