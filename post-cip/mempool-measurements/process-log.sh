#!/usr/bin/env bash

set -eo pipefail

SCRIPT_DIR="$(dirname "${BASH_SOURCE[0]}")"

LOGFILE="$1"

sed -n -e '/cardano\.node\.Mempool.*"TraceMempoolAddedTx"/{s/^.* .\([0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\} [0-9]\{2\}:[0-9]\{2\}:[0-9]\{2\}[^]]*\)].*("tx",Object (fromList \[\(.*\)]))]$/\1\t\2/;s/("txid",String "\(........\)")/\1/g;p}' -e '1iTimestamp\tTxId' "$LOGFILE" > tx_times.tsv

sed -n -e '/cardano\.node\.ChainDB.*new tip:/{s/^.* .\([0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\} [0-9]\{2\}:[0-9]\{2\}:[0-9]\{2\}[^]]*\)].*new tip: \(................................................................\) at slot \(.........\).*/\1\t\2\t\3/;p}' -e '1iTimestamp\tBlock\tSlot' "$LOGFILE" > block_times.tsv

psql -h thelio -f "$SCRIPT_DIR/process-log.sql" mainnet

gzip -9fv *.tsv
