#!/usr/bin/env bash

set -eo pipefail

if true
then
  ulimit \
    -m $(($(sed -n -e '/^MemTotal:/{s/^[^ ]* *\([^ ]*\) .*$/\1/;p}' /proc/meminfo) *  85 / 100)) \
    -v $(($(sed -n -e '/^MemTotal:/{s/^[^ ]* *\([^ ]*\) .*$/\1/;p}' /proc/meminfo) * 115 / 100)) \
    -S
fi

for SCENARIO in 2MB 12MB
do

  if [ ! -f scenario-$SCENARIO.yaml ]
  then
    sed -e "/-- $SCENARIO scenario/s/^--/  /" utxo-dag.sql \
    | psql mainnet
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

  `which time` --verbose python main.py \
    --log-solver \
    --out-yaml results-$SCENARIO.yaml \
    --out-trace results-$SCENARIO.json \
    scenario-$SCENARIO.yaml \
  |& tee results-$SCENARIO.log

  if [ ! -f scenario-$SCENARIO-adv.yaml ]
  then
    sed -e 's/^  delta_rh:.*/  delta_rh: 1000000/' \
        -e 's/^  delta_rb:.*/  delta_rb: 5000000/' \
        -e 's/^  delta_eh:.*/  delta_eh: 10000000/' \
        -e '/^    arrival_delay: [1-9]/s/^    arrival_delay:.*/    arrival_delay: 20000000/' \
        scenario-$SCENARIO.yaml \
    > scenario-$SCENARIO-adv.yaml
  fi

  `which time` --verbose python main.py \
    --log-solver \
    --out-yaml results-$SCENARIO-adv.yaml \
    --out-trace results-$SCENARIO-adv.json \
    scenario-$SCENARIO-adv.yaml \
  |& tee results-$SCENARIO-adv.log

done

