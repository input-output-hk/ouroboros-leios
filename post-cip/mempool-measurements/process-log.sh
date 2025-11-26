#!/usr/bin/env bash

set -eo pipefail

SCRIPT_DIR="$(dirname "${BASH_SOURCE[0]}")"

echo $'Region\tTimestamp\tTxId' > tx-times.tsv
echo $'Region\tTimestamp\tBlock\tSlot' > block-times.tsv

for region in eu-central-1 us-east-2 ap-northeast-1
do
  sed -n -e '/cardano\.node\.Mempool.*"TraceMempoolAddedTx"/{s/^.* .\([0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\} [0-9]\{2\}:[0-9]\{2\}:[0-9]\{2\}[^]]*\)].*("tx",Object (fromList \[\(.*\)]))]$/'"$region"'\t\1\t\2/;s/("txid",String "\(........\)")/\1/g;p}' "$region"/2025-*.log >> tx-times.tsv
  sed -n -e '/cardano\.node\.ChainDB.*new tip:/{s/^.* .\([0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\} [0-9]\{2\}:[0-9]\{2\}:[0-9]\{2\}[^]]*\)].*new tip: \(................................................................\) at slot \(.........\).*/'"$region"'\t\1\t\2\t\3/;p}' "$region"/2025-*.log >> block-times.tsv
done

psql -f "$SCRIPT_DIR/process-log.sql" mainnet

gzip -9fv *.tsv
