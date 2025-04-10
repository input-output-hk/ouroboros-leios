#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq dasel gnused gzip

IDX=$(mktemp --tmpdir=$PWD --suffix=.json)
function cleanup {
  rm "$IDX"
}
trap cleanup EXIT

jq -c '
  select(.message.type | IN(
    "IBGenerated",
    "EBGenerated",
    "VTBundleGenerated",
    "RBGenerated"
  ))
| {
    "\(.message.type[0:2] + "|" + .message.id)": {
      "producer": .message.producer,
      "sent": .time_s,
      "size": (.message.total_bytes // .message.bytes)
    }
  }
' "$1" \
| jq --slurp 'add
' > "$IDX"

jq --slurpfile idx "$IDX" -c '
  select(.message.type | IN(
    "IBReceived",
    "EBReceived",
    "VTBundleReceived",
    "RBReceived"
  ))
| {
    "kind": .message.type[0:2],
    "item": .message.id,
    "recipient": .message.recipient,
    "received": .time_s
  }
| (. + $idx[0][.kind + "|" + .item])
| (. + {elapsed: (.received - .sent)})
' "$1" \
| sort \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
| gzip -9c \
> "$2"
