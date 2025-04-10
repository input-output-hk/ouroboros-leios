#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq dasel gnused gzip

jq -c '
  select(.message.type == "Cpu")
| {
    "idx": {
      "slot": (.time_s | floor),
      "node": .message.node,
      "task": .message.task_label
    },
    "duration": .message.cpu_time_s
  }
' "$1" \
| sort \
| jq -sc '
  group_by(.idx)
| map(.[0].idx + {"duration": (map(.duration) | add)})
| .[]
' \
| dasel -r json -w csv \
| sed -n -e '1p;0~2p' \
| gzip -9c \
> "$2"
