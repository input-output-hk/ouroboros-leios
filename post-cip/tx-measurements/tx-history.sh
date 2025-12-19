#!/usr/bin/env bash

psql -f tx-history.sql mainnet

pigz -9fv *.tsv

zcat utxo-history.tsv.gz \
| gawk '
BEGIN {
  FS = "\t"
  OFS = "\t"
}
FNR == 1 {
  print "utxo_id16", "tx_create_id", "tx_spend_id", "slots", "blocks"
}
FNR > 1 && $3 != "" {
  print substr($1, 0, 16) substr($1, 65), $2, $3, $5 - $4, $7 - $6
}
' \
| pigz -9c \
> history-graph.tsv.gz

(
  zcat history-graph.tsv.gz | head -n 1
  zcat history-graph.tsv.gz | tail -n +2 | sort -k4,4n --parallel=12 -S 50G
) | pigz -9c > history-graph-sorted-slot.tsv.gz


(
  zcat history-graph.tsv.gz | head -n 1
  zcat history-graph.tsv.gz | tail -n +2 | sort -k5,5n --parallel=12 -S 50G
) | pigz -9c > history-graph-sorted-block.tsv.gz

rm history-graph.tsv.gz

