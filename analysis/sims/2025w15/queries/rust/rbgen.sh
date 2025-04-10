#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq dasel gnused gzip

jq -c '
  select(.message.type == "RBGenerated")
| {
    "rb": .message.id,
    "time": .time_s,
    "size": "NA",
    "eb-count": (if .message.endorsement == null then 0 else 1 end)
  }
' "$1" \
| sort \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
| gzip -9c \
> "$2"
