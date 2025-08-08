
TX_ID=80921

zcat sim.log.gz \
| grep '"TXGenerated".*"id":"'"$TX_ID"'"' \
| jq -c '.
  | select(.message.type == "TXGenerated")
  | select(.message.id == "'"$TX_ID"'")
  | { time_s, tx: .message.id, node: .message.publisher }
' \
| tee tx-generated.jsonl \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
> tx-generated.csv

zcat sim.log.gz \
| grep '"TXReceived".*"id":"'"$TX_ID"'"' \
| jq -c '.
  | select(.message.type == "TXReceived")
  | select(.message.id == "'"$TX_ID"'")
  | { time_s, tx: .message.id, node: .message.recipient }
' \
| tee tx-received.jsonl \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
> tx-received.csv

zcat sim.log.gz \
| grep '"EBGenerated".*"transactions":\[.*{"id":"'"$TX_ID"'"}' \
| jq -c '.
  | select(.message.type == "EBGenerated")
  | {time_s, node: .message.producer, eb: .message.id}
' \
| tee eb-generated.jsonl \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
> eb-generated.csv

zcat sim.log.gz \
| grep -E '"EBReceived".*"id":"('"$(jq -rs 'map(.eb) | join("|")' eb-generated.jsonl)"')"' \
| jq -c '.
  | select(.message.type == "EBReceived")
  | { time_s, eb: .message.id, recipient: .message.recipient }
' \
| tee eb-received.jsonl \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
> eb-received.csv

zcat sim.log.gz \
| grep -E '"VTBundleGenerated".*"votes":{.*"('"$(jq -rs 'map(.eb) | join("|")' eb-generated.jsonl)"')"' \
| jq -c '.
  | select(.message.type == "VTBundleGenerated")
  | .time_s as $time_s
  | .message.id as $vote
  | .message.producer as $node
  | .message.votes
  | to_entries
  | .[]
  | { time_s: $time_s, node: $node, vote: $vote, eb: .key, weight: .value }
' \
| tee vt-generated.jsonl \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
> vt-generated.csv

zcat sim.log.gz \
| grep -E '"VTBundleReceived".*"id":"('"$(jq -rs 'map(.vote) | join("|")' vt-generated.jsonl)"')"' \
| jq -c '.
  | select(.message.type == "VTBundleReceived")
  | { time_s, vote: .message.id, recipient: .message.recipient }
' \
| tee vt-received.jsonl \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
> vt-received.csv

zcat sim.log.gz \
| grep '"RBGenerated"' \
| jq -c '.
  | select(.message.type == "RBGenerated")
  | {
      time_s,
      node: .message.producer,
      rb: .message.id,
      parent: .message.parent.id,
      eb: (if .message.endorsement then .message.endorsement.eb.id else "NA" end),
      has_tx: (.message.transactions | contains(["'"$TX_ID"'"]))
    }
' \
| tee rb-generated.jsonl \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
> rb-generated.csv

zcat sim.log.gz \
| grep '"RBReceived"' \
| jq -c '.
  | select(.message.type == "RBReceived")
  | { time_s, rb: .message.id, recipient: .message.recipient }
' | tee rb-received.jsonl \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
> rb-received.csv

