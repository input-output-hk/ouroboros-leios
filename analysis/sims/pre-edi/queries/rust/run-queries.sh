#!/usr/bin/env bash

DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

source "$DIR/../../env.sh"

mongo --host "$HOST" "$DB" \
  "$DIR/scenario.js" \
  "$DIR/cpus.js" \
  "$DIR/ib2ebs.js" \
  "$DIR/eb2rbs.js" \
  "$DIR/ibgen.js" \
  "$DIR/ebgen.js" \
  "$DIR/rbgen.js" \
  "$DIR/receipts.js"
