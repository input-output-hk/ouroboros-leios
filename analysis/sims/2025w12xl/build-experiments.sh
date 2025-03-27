#!/usr/bin/env bash

set -ev

LABEL=default
NETWORK=realistic
MAX_SLOT=600

for SIMULATOR in haskell rust
do
  for IB_RATE in 0.3 3.0 30.0
  do
    for IB_SIZE in 32768 98304 163840
    do
      for EB_RATE in 1.5
      do
        for STAGE_LENGTH in 60
        do
          ./make-experiment.sh $SIMULATOR $MAX_SLOT $LABEL $NETWORK $IB_RATE $IB_SIZE $EB_RATE $STAGE_LENGTH
        done
      done
    done
  done
done
