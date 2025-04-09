#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq dasel gnused gzip

jq -c '
  select(.message.type == "EBGenerated")
| {
    "eb": .message.id,
    "node": .message.producer,
    "time": .time_s,
    "size": .message.bytes,
    "ib-count": (.message.input_blocks | length)
  }
' "$1" \
| sort \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
> "$2"
