#!/usr/bin/env bash

/usr/local/bin/sim-cli-release \
  --slots 120 \
  --conformance-events \
  --parameters config.yaml \
  network.yaml \
  /dev/null
