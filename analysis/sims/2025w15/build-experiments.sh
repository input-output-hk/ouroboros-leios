#!/usr/bin/env bash

set -ev

MAX_SLOT=600

for SIMULATOR in rust haskell
do
  for LABEL in default
  do
    for NETWORK in 100-nodes
    do
      for IB_RATE in 1.0 1.5 2.0 2.5 3.0 3.5 4.0 4.5 5.0 5.5 6.0 6.5 7.0 7.5 8.0 8.5 9.0 9.5 10.0
      do
        for IB_SIZE in 98304
        do
          for EB_RATE in 1.5
          do
            for STAGE_LENGTH in 20
            do
              ./make-experiment.sh $SIMULATOR $MAX_SLOT $LABEL $NETWORK $IB_RATE $IB_SIZE $EB_RATE $STAGE_LENGTH
            done
          done
        done
      done
    done
  done
done
