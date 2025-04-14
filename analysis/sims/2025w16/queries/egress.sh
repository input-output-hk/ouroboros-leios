#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq dasel gnused gzip

IDX=$(mktemp --tmpdir=$PWD --suffix=.json)
function cleanup {
  rm "$IDX"
}
trap cleanup EXIT

jq -c '
  select(.message.type | match("Generated$"))
| {
    "\(.message.type[0:2] + "|" + .message.id)": {
      size: .message.size_bytes
    }
  }
' "$1" \
| jq --slurp 'add
' > "$IDX"

jq --slurpfile idx "$IDX" -c '
  select(.message.type | match("Sent$"))
| {
    "kind": .message.type[0:2],
    "item": .message.id,
    "sender": .message.sender
  }
| (. + $idx[0][.kind + "|" + .item])
| {
    idx: {sender, kind},
    size
  }
' "$1" \
| jq --slurp -c '
  group_by(.idx)
  | map(.[0].idx + {"size": (map(.size) | add)})
  | .[]
' \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
| gzip -9c \
> "$2"
