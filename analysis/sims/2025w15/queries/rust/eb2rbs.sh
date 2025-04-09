#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq dasel gnused gzip

jq -c '
  select(.message.type == "RBGenerated" and .message.endorsement)
| {
    "eb": .message.endorsement.eb.id,
    "rb": .message.id
  }
' "$1" \
| sort \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
> "$2"
