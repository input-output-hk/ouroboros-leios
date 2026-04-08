#!/usr/bin/env bash
# Print a one-line-per-node summary of cluster chain progress.
#
# Usage: scripts/cluster-status.sh [aggregator_port]
#
# Highlights nodes that are stuck (tip_block_no < max_tip - LAG_THRESHOLD).

set -euo pipefail

PORT="${1:-9100}"
LAG_THRESHOLD="${LAG_THRESHOLD:-3}"

JSON="$(curl -sS "http://localhost:${PORT}/api/stats")"
LAG_THRESHOLD="$LAG_THRESHOLD" CLUSTER_JSON="$JSON" python3 <<'PY'
import json, os, sys

threshold = int(os.environ['LAG_THRESHOLD'])
data = json.loads(os.environ['CLUSTER_JSON'])

nodes = []
for node_id, s in data.items():
    try:
        idx = int(node_id.split('-')[1])
    except (IndexError, ValueError):
        idx = 1 << 30
    nodes.append((idx, node_id, s))
nodes.sort()

if not nodes:
    print("(no nodes reporting)")
    sys.exit(0)

max_tip = max(s.get('tip_block_no') or 0 for _, _, s in nodes)
max_slot = max(s.get('slot') or 0 for _, _, s in nodes)

print(f"max tip = block#{max_tip}    max slot = {max_slot}    {len(nodes)} nodes")
print("-" * 78)
print(f"{'node':<10}{'tip':>6}{'lag':>6}{'slot':>14}{'prod':>7}{'rcvd':>8}{'val':>7}  peers")

stuck = []
for _, node_id, s in nodes:
    tip = s.get('tip_block_no') or 0
    slot = s.get('slot') or 0
    prod = s.get('blocks_produced') or 0
    rcvd = s.get('blocks_received') or 0
    val = s.get('blocks_validated') or 0
    peer_count = s.get('peer_count') or 0
    lag = max_tip - tip
    marker = " <-- STUCK" if lag >= threshold else ""
    if lag >= threshold:
        stuck.append((node_id, tip, lag))
    print(f"{node_id:<10}{tip:>6}{lag:>6}{slot:>14}{prod:>7}{rcvd:>8}{val:>7}{'':>3}{peer_count}{marker}")

print("-" * 78)
if stuck:
    print(f"{len(stuck)} stuck node(s) (lag >= {threshold}): " +
          ", ".join(f"{n} (block#{t}, lag {l})" for n, t, l in stuck))
else:
    print(f"all nodes within {threshold} of tip")
PY
