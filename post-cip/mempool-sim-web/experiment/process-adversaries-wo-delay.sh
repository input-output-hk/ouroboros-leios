#!/usr/bin/env bash

set -euo pipefail
shopt -s nullglob

files=(adversaries-wo-delay-[0-9]*.jsonl.gz)
all=(adversaries-wo-delay-*.jsonl.gz)

if [ "${#files[@]}" -eq 0 ]
then
  echo "No no-delay adversary run files found (expected adversaries-wo-delay-<N>.jsonl.gz)." >&2
  exit 1
fi

# Guard against stale/mixed files from other runs.
for f in "${all[@]}"
do
  if [[ ! "$f" =~ ^adversaries-wo-delay-[0-9]+\.jsonl\.gz$ ]]
  then
    echo "Unexpected file '$f' in experiment directory; clean stale artifacts first." >&2
    exit 1
  fi
done

for f in "${files[@]}"
do
  eb_mode=$(zcat "$f" | jq -r 'first | (.eb // empty)')
  if [ -z "$eb_mode" ]
  then
    echo "File '$f' is missing configuration metadata (.eb)." >&2
    exit 1
  fi
  if [ "$eb_mode" != "false" ]
  then
    echo "No-delay experiment expects Praos-style inputs only (.eb=false), got '$eb_mode' in '$f'." >&2
    exit 1
  fi
done

(

echo $'Adversarial nodes\tRB ID\tRB honest txs\tRB adversarial txs\tEB ID\tEB honest txs\tEB adversarial txs'
for f in "${files[@]}"
do
  zcat "$f" \
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

) | gzip -9c > adversaries-wo-delay.tsv.gz
