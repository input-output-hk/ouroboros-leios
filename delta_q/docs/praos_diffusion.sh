#!/bin/bash

# usage: praos_diffusion.sh <json_file>

# Reads a JSON output file from the Haskell simulation of Praos,
# converts the arrival times of each block into a CDF,
# and outputs the CDFs in a format suitable for the web app.

# The individual traces are considered as representations of
# different possible diffusion patterns and are thus combined
# using the probabilistic choice operator.

jq -rf convert_arrivals.jq < "$1" |
(
  while read CDF; do
    if [ -z "$RET" ]; then
      RET="$CDF"
      N=1
    else
      RET="$CDF\n1<>$N\n$RET"
      let N++
    fi
  done
  echo -e "$RET"
)
