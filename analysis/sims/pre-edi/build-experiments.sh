#!/usr/bin/env bash

set -ev


LABEL=default
NETWORK=100-nodes
IB_SIZE=98304
MAX_SLOT=600

for SIMULATOR in haskell rust
do
  for IB_RATE in 1.0 5.0 10.0 15.0 20.0 25.0
  do
    for EB_RATE in 1.0 1.5 2.0 2.5
    do
      for STAGE_LENGTH in 20 40 60
      do
        ./make-experiment.sh $SIMULATOR $MAX_SLOT $LABEL $NETWORK $IB_RATE $IB_SIZE $EB_RATE $STAGE_LENGTH
      done
    done
  done
done


LABEL=default
IB_SIZE=98304
EB_RATE=1.5
STAGE_LENGTH=20
MAX_SLOT=600

for SIMULATOR in haskell rust
do
  for NETWORK in 100-nodes-1cpus 100-nodes-2cpus 100-nodes-4cpus 100-nodes-8cpus 100-nodes-16cpus
  do
    for IB_RATE in 1.0 5.0 10.0 15.0 20.0 25.0
    do
    ./make-experiment.sh $SIMULATOR $MAX_SLOT $LABEL $NETWORK $IB_RATE $IB_SIZE $EB_RATE $STAGE_LENGTH
    done
  done
done


NETWORK=100-nodes
IB_SIZE=98304
EB_RATE=1.5
STAGE_LENGTH=20
MAX_SLOT=600

for SIMULATOR in haskell rust
do
  for LABEL in default extended-voting oldest-first peer-order
  do
    for IB_RATE in 1.0 5.0 10.0 15.0 20.0 25.0
    do
      ./make-experiment.sh $SIMULATOR $MAX_SLOT $LABEL $NETWORK $IB_RATE $IB_SIZE $EB_RATE $STAGE_LENGTH
    done
  done
done
