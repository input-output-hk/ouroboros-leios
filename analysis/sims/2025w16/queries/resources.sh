#!/usr/bin/env nix-shell
#!nix-shell -i bash -p jq dasel gnused gzip

IDX=$(mktemp --tmpdir=$PWD --suffix=.json)
EGR=$(mktemp --tmpdir=$PWD --suffix=.json)
DSK=$(mktemp --tmpdir=$PWD --suffix=.json)
function cleanup {
  rm "$IDX" "$EGR" "$DSK"
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
    sender,
    size
  }
' "$1" \
| jq --slurp '
  group_by(.sender)
  | map({"\(.[0].sender)": (map(.size) | add)})
  | add
' > "$EGR"

jq -c '
  select(.message.type | match("(RBGenerated|EBGenerated|IBGenerated)$"))
| {
    "size": .message.size_bytes
  }
' "$1" \
| jq --slurp -c '
  map(.size)
| add
' \
> "$DSK"

jq -c '
  select(.message.type == "Cpu")
| {
    "idx": {
      "slot": (.time_s | floor),
      "node": .message.node
    },
    "duration": .message.cpu_time_s
  }
' "$1" \
| sort \
| jq --slurpfile egr "$EGR" --slurpfile dsk "$DSK" -sc '
  group_by(.idx)
| map(.[0].idx + {"duration": (map(.duration) | add)})
| group_by(.node)
| map({
    "node": .[0].node,
    "egress": $egr[0][.[0].node],
    "disk": $dsk[0],
    "total_cpu": (map(.duration) | add),
    "maximum_cpu": (map(.duration) | max)
  })
| .[]
' \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
| gzip -9c \
> "$2"
