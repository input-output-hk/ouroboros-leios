#!/usr/bin/env nix-shell
#!nix-shell -i bash -p jq dasel gnused gzip

jq -c '
  select(.message.type | match("(RB|EB|IB|VTBundle)Generated$"))
| (.message.type[0:2] + "|" + .message.id) as $from
| (.time_s) as $time
| if .message.type == "IBGenerated" then
    [
      .message.transactions.[] | {
        from: $from,
        to: ("TX|" + .),
        time: $time
      }
    ]
  elif .message.type == "EBGenerated" then
    [
      .message.input_blocks.[] | {
        from: $from,
        to: ("IB|" + .id),
        time: $time
      }
    ] + [
    .message.endorser_blocks.[] | {
        from: $from,
        to: ("EB|" + .id),
        time: $time
      }
    ]
  elif .message.type == "RBGenerated" and .message.endorsement then
    [
      {
        from: $from,
        to: ("RB|" + .message.parent.id),
        time: $time
      }
    ] + [
      {
        from: $from,
        to: ("EB|" + .message.endorsement.eb.id),
        time: $time
      }
    ]
  elif .message.type == "RBGenerated" then
    [
      {
        from: $from,
        to: ("RB|" + .message.parent.id),
        time: $time
      }
    ]
  elif .message.type == "VTBundleGenerated" then
    [
      .message.votes | keys .[] | {
        from: $from,
        to: ("EB|" + .),
        time: $time
      }
    ]
  else
    []
  end
| .[]
' "$1" \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
| gzip -9c \
> "$2"
