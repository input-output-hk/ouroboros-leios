#!/usr/bin/env bash

source env.sh

mongo --host "$HOST" "$DB" \
  queries/haskell/receipts.js \
  queries/haskell/cpus.js \
  queries/haskell/ib2ebs.js \
  queries/haskell/eb2rbs.js \
  queries/haskell/ibgen.js \
  queries/haskell/ebgen.js \
  queries/haskell/rbgen.js
