#!/usr/bin/env bash

set -eo pipefail

(

echo $'Adversarial nodes\tType\tID\tTxs\tHonest txs\tAdversarial txs'
for f in adversaries-*.jsonl.gz
do
  zcat $f \
| jq -rs '
    .[0].adversaries as $adversaries
  | .[]
  | select(.msg == "block produced")
  | (
      [$adversaries, "RB", .blockId, .txCount, .honestCount, .adversarialCount],
      (
        .certifiedEB as $eb
        | select($eb != null)
        | [$adversaries, "EB", $eb.ebId, (($eb.txRefs // []) | length), $eb.honestCount, $eb.adversarialCount]
      )
    )
  | @tsv
'
done

) | gzip -9c > adversaries.tsv.gz
