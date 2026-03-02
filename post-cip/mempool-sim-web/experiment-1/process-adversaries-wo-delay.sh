#!/usr/bin/env bash

set -eo pipefail

(

echo $'Adversarial nodes\tBlock ID\tTxs\tHonest txs\tAdversarial txs'
for f in adversaries-wo-delay-*.jsonl.gz
do
  zcat $f \
| jq -rs '
    .[0].adversaries as $adversaries
  | .[]
  | select(.msg == "block produced")
  | [$adversaries, .blockId, .txCount, .honestCount, .adversarialCount]
  | @tsv
'
done

) | gzip -9c > adversaries-wo-delay.tsv.gz
