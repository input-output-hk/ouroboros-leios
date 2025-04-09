#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq dasel gnused gzip

jq -c '
  select(.message.type == "RBGenerated")
| {
    "time": .time_s,
    "rb": .message.id,
    "eb-count": (if .message.endorsement == null then 0 else 1 end)
  }
' "$1" \
| sort \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
> "$2"
