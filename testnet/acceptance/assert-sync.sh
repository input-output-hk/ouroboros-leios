#!/usr/bin/env bash
#
# Assertion for the ShelleyBlock byte-preservation hotfix.
#
# Polls both nodes' tips via cardano-cli. Passes once nodeB has selected a
# chain that:
#   * is past the contentious block 67555 (Dijkstra RB, header hash
#     70c34f39cf63c8fe9c0f645ef1c6ea3edcf6f72944af43d3eaaf3b40d252761e), and
#   * matches nodeA at the current tip (same hash and block number).
#
# Without the hotfix nodeA re-encodes block 67555 on disk-write, then serves
# a re-encoded body over BlockFetch whose bytes no longer match the header's
# committed hbBodySize/hbBodyHash — nodeB rejects the block and the chain
# cannot advance past 67554. With the hotfix nodeA preserves the wire bytes
# and nodeB validates cleanly.

set -euo pipefail

: "${SOCKET_A:?SOCKET_A required (nodeA cardano-node socket path)}"
: "${SOCKET_B:?SOCKET_B required (nodeB cardano-node socket path)}"
: "${NETWORK_MAGIC:=164}"
: "${TARGET_BLOCK:=67556}"
: "${TIMEOUT:=1800}"
: "${POLL_INTERVAL:=5}"

query_tip() {
  local socket=$1
  CARDANO_NODE_SOCKET_PATH="$socket" \
    cardano-cli query tip --testnet-magic "$NETWORK_MAGIC" 2>/dev/null \
    || echo '{}'
}

start=$SECONDS
while true; do
  elapsed=$((SECONDS - start))
  if (( elapsed > TIMEOUT )); then
    echo "acceptance: FAIL — timed out after ${elapsed}s waiting for nodeB to sync past block $TARGET_BLOCK"
    exit 1
  fi

  tipA=$(query_tip "$SOCKET_A")
  tipB=$(query_tip "$SOCKET_B")
  bA=$(jq -r '.block // 0' <<<"$tipA")
  bB=$(jq -r '.block // 0' <<<"$tipB")
  hA=$(jq -r '.hash // ""' <<<"$tipA")
  hB=$(jq -r '.hash // ""' <<<"$tipB")

  printf '[%4ds] nodeA=%s@%s nodeB=%s@%s\n' \
    "$elapsed" "$bA" "${hA:0:8}" "$bB" "${hB:0:8}"

  if [[ "$bB" -ge "$TARGET_BLOCK" && "$hA" == "$hB" && -n "$hA" ]]; then
    echo "acceptance: PASS — nodeB selected chain at block $bB (past contentious 67555), tip matches nodeA"
    continue
  fi

  sleep "$POLL_INTERVAL"
done
