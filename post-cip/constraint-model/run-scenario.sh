#!/usr/bin/env bash

set -eo pipefail

SCENARIO=12MB

if [ ! -f scenario-$SCENARIO.yaml ]
then
  psql -f utxo-dag.sql mainnet
  json2yaml scenario.json > scenario-$SCENARIO.yaml
  jq -cr '
    .dag
  | to_entries  
  | [
      .[]
    | .value
    | select(.type != "LG")
    | (.cost_verify + .cost_apply + .cost_reapply)
    ]
  | add
  ' scenario.json
  rm scenario.json
fi

ulimit \
  -m $(($(sed -n -e '/^MemTotal:/{s/^[^ ]* *\([^ ]*\) .*$/\1/;p}' /proc/meminfo) *  85 / 100))$MEM \
  -v $(($(sed -n -e '/^MemTotal:/{s/^[^ ]* *\([^ ]*\) .*$/\1/;p}' /proc/meminfo) * 125 / 100))$MEM \
  -S

nice python main.py \
  --log-solver \
  --out-yaml results-$SCENARIO.yaml \
  --out-trace results-$SCENARIO.json \
  scenario-$SCENARIO.yaml

