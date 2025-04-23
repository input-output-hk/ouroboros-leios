#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq dasel gnused gzip

IDX=$(mktemp --tmpdir=$PWD --suffix=.json)
function cleanup {
  rm "$IDX"
}
trap cleanup EXIT

jq -c '
  select(.message.type == "RBGenerated")
| .message.endorsements[]
| {
    "eb": .eb.id
  }
' "$1" \
| sort \
| jq --slurp '
  group_by(.eb)
  | map({"\(.[0].eb)": (. | length)})
| add
' > "$IDX"

jq --slurpfile idx "$IDX" -c '
  select(.message.type == "EBGenerated")
| {
    "eb": .message.id,
    "node": .message.producer,
    "time": .time_s,
    "size": .message.bytes,
    "ib-count": (.message.input_blocks | length),
    "eb-count": "NA",
    "rb-count": ($idx[0][.message.id] // 0)
  }
' "$1" \
| sort \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
| gzip -9c \
> "$2"
