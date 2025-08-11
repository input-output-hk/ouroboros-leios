#!/usr/bin/env bash

jq -r '.
  | .nodes
  | to_entries
  | .[]
  | select(.value.stake > 0)
  | .key + "\t" + (.value.stake | tostring)
' ../../../../data/simulation/pseudo-mainnet/topology-v2.yaml \
> stake.tsv

TOTAL=$(gawk 'BEGIN {FS = "\t"} {total += $2} END {print total}' stake.tsv)

TARGET=$((TOTAL / 3))

gawk -v target=$TARGET '
BEGIN {
  FS = "\t"
  total = 0
}
total < target {
  total += $2
  if (total <= target)
    print $1
}
' stake.tsv > adversary.tsv
