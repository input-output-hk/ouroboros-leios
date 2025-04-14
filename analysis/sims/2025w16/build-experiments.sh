#!/usr/bin/env bash

set -ev

MAX_SLOT=600

for SIMULATOR in rust haskell
do
  for LABEL in default
  do
    for NETWORK in 100-nodes
    do
      for IB_RATE in 0.5 1.0 2.0 4.0 8.0 16.0
      do
        for IB_SIZE in 65536 131072 
        do
          for EB_RATE in 1.0 1.5 2.0
          do
            for STAGE_LENGTH in 10 20 40
            do
              ./make-experiment.sh $SIMULATOR $MAX_SLOT $LABEL $NETWORK $IB_RATE $IB_SIZE $EB_RATE $STAGE_LENGTH
            done
          done
        done
      done
    done
  done
done
