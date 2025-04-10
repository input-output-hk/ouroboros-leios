#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq dasel gnused gzip

IDX=$(mktemp --tmpdir=$PWD --suffix=.json)
function cleanup {
  rm "$IDX"
}
trap cleanup EXIT

jq -c '
  select(.message.type == "EBGenerated")
| . as $x
| .message.input_blocks[]
| {
    "ib": .id,
    "eb": $x.message.id,
  }
' "$1" \
| jq --slurp '
  group_by(.ib)
| map({"\(.[0].ib)": (. | length)})
| add
' > "$IDX"

jq -c --slurpfile idx "$IDX" '
  select(.message.type == "IBGenerated")
| {
    "ib": .message.id,
    "node": .message.producer,
    "time": .time_s,
    "size": .message.total_bytes,
    "eb-count": ($idx[0][.message.id] // 0)
  }
' "$1" \
| sort \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
| gzip -9c \
> "$2"
