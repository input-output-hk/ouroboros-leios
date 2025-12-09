#!/usr/bin/env bash

set -eo pipefail

SCRIPT_DIR="$(dirname "${BASH_SOURCE[0]}")"


(
  echo $'Remote\tLongitude [deg]\tLatitude [deg]'
  zcat reallyfreegeoip.jsonl.gz | jq -r '.ip + "\t" + (.longitude | tostring) + "\t" + (.latitude | tostring)'
) > reallyfreegeoip.tsv


echo $'Region\tTimestamp\tTxId' > tx-times.tsv
echo $'Region\tTimestamp\tBlock\tSlot' > block-times.tsv
echo $'Region\tTimestamp\tLocal\tRemote\tTxId 1\tTxId 2' > outbounds.tsv

for region in eu-central-1 us-east-2 ap-northeast-1
do
  zcat "$region"/2025-*.log.gz \
  | sed -n -e '/cardano\.node\.Mempool.*"TraceMempoolAddedTx"/{s/^.* .\([0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\} [0-9]\{2\}:[0-9]\{2\}:[0-9]\{2\}[^]]*\)].*("tx",Object (fromList \[\(.*\)]))]$/'"$region"'\t\1\t\2/;s/("txid",String "\(........\)")/\1/g;p}' \
        >> tx-times.tsv
  zcat "$region"/2025-*.log.gz \
  | sed -n -e '/cardano\.node\.ChainDB.*new tip:/{s/^.* .\([0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\} [0-9]\{2\}:[0-9]\{2\}:[0-9]\{2\}[^]]*\)].*new tip: \(................................................................\) at slot \(.........\).*/'"$region"'\t\1\t\2\t\3/;p}'\
        >> block-times.tsv
  zcat "$region"/2025-*.log.gz \
  | sed -E \
        -e '/cardano.node.TxOutbound:.*"TxSubmissionOutboundRecvMsgRequestTxs"/!d' \
        -e 's/^.*:cardano.node.TxOutbound:Info:.* .([[:digit:]]{4}-[[:digit:]]{2}-[[:digit:]]{2} [[:digit:]]{2}:[[:digit:]]{2}:[[:digit:]]{2})\.[[:digit:]]{2} UTC]/'"$region"'\t\1\t/' \
        -e 's/\t[^\t]*\("local",Object \(fromList \[\("addr",String "([[:digit:]]{1,3}\.[[:digit:]]{1,3}\.[[:digit:]]{1,3}\.[[:digit:]]{1,3})"\),\("port",String "([[:digit:]]{1,5})"\)\]\)\)/\t\1:\2\t/' \
        -e 's/\t,\("remote",Object \(fromList \[\("addr",String "([[:digit:]]{1,3}\.[[:digit:]]{1,3}\.[[:digit:]]{1,3}\.[[:digit:]]{1,3})"\),\("port",String "([[:digit:]]{1,5})"\)\]\)\)/\t\1:\2\t/' \
        -e 's/\t[^\t]*\("txIds",String "\[HardForkGenTxId \{getHardForkGenTxId = S \(S \(S \(S \(S \(S \(Z \(WrapGenTxId \{unwrapGenTxId = txid: TxId \{unTxId = SafeHash \\"([[:xdigit:]]{64})\\"\}\}\)\)\)\)\)\)\)\}\]"\)\]/\t\1\t/' \
        -e 's/\t[^\t]*\("txIds",String "\[HardForkGenTxId \{getHardForkGenTxId = S \(S \(S \(S \(S \(S \(Z \(WrapGenTxId \{unwrapGenTxId = txid: TxId \{unTxId = SafeHash \\"([[:xdigit:]]{64})\\"\}\}\)\)\)\)\)\)\)\},HardForkGenTxId \{getHardForkGenTxId = S \(S \(S \(S \(S \(S \(Z \(WrapGenTxId \{unwrapGenTxId = txid: TxId \{unTxId = SafeHash \\"([[:xdigit:]]{64})\\"\}\}\)\)\)\)\)\)\)\}\]"\)\]/\t\1\t\2/' \
        >> outbounds.tsv
done

psql -f "$SCRIPT_DIR/process-log.sql" mainnet

gzip -9fv *.tsv
