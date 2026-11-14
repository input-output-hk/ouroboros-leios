#!/usr/bin/env bash
# Tallies, from each node's log, what crossed the relay.
#
# Expects WORKING_DIR to be set.
set -uo pipefail

: "${INTERVAL:=10}"

count() {
  local log="$WORKING_DIR/$1/node.log" pattern="$2"
  [ -f "$log" ] || {
    echo 0
    return
  }
  grep -cF "$pattern" "$log" || true
}

while true; do
  date -u +"%H:%M:%S"
  printf '  %-6s %10s %8s %15s %10s\n' node announced voted votes-received certified
  for node in node1 node2 node3; do
    announced=$(count "$node" 'LeiosKernel.BlockAnnounced\"')
    voted=$(count "$node" 'LeiosKernel.Voted\"')
    received=$(count "$node" 'LeiosNotify.Remote.Receive.Votes\"')
    certified=$(count "$node" 'LeiosKernel.BlockCertified\"')
    printf '  %-6s %10s %8s %15s %10s\n' "$node" "$announced" "$voted" "$received" "$certified"
  done
  sleep "$INTERVAL"
done
