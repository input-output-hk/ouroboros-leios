#!/usr/bin/env nix-shell
#!nix-shell -i bash -p jq dasel gnused gzip

jq -c '
  select(.message.type | match("(RB|EB|IB|VTBundle|TX)Generated$"))
| (.message.producer // .message.publisher) as $node
| .time_s as $time
| .message.size_bytes as $size
| if .message.type == "VTBundleGenerated" then
    [
      .message.votes | keys | .[] | {
        id: ("VT|" + .),
        kind: "VT",
        node: $node,
        time: $time,
        size: $size
      }
    ]
  else
    [
      {
        id: (.message.type[0:2] + "|" + .message.id),
        kind: .message.type[0:2],
        node: $node,
        time: $time,
        size: $size
      }
    ]
  end
| .[]
' "$1" \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
| gzip -9c \
> "$2"
