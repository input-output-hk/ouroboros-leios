#!/usr/bin/env bash
# Full cluster health + Leios pipeline check.
# Usage: scripts/cluster-check.sh [aggregator_port]

set -uo pipefail

PORT="${1:-9100}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
LOGS="$ROOT/logs"
EVENTS="$ROOT/cluster-events.jsonl"

echo "=== Cluster Status ==="
bash "$SCRIPT_DIR/cluster-status.sh" "$PORT"
echo ""

echo "=== TX Generation (node-0) ==="
count=$(grep -c "generated transaction" "$LOGS/node-0.log" 2>/dev/null || echo 0)
echo "  $count txs generated"
echo ""

echo "=== Leios Pipeline (all nodes) ==="
for stat in "produced endorser" "eb election created" "vote produced" "quorum reached"; do
  total=$(grep -ch "$stat" "$LOGS"/node-*.log 2>/dev/null | awk '{s+=$1}END{print s+0}')
  printf "  %-25s %s\n" "$stat:" "$total"
done
echo ""

echo "=== Recent Blocks ==="
grep "produced block" "$LOGS"/node-*.log 2>/dev/null | sort -t= -k2 | tail -5 | sed 's|.*/logs/||'
echo ""

echo "=== Telemetry Summary ==="
[ -f "$EVENTS" ] && python3 -c "
import json
from collections import Counter
c = Counter()
for line in open('$EVENTS'):
    try: c[json.loads(line)['message']['type']] += 1
    except: pass
for k in ['RBGenerated','EBGenerated','EBReceived','VotesReceived','BlockValidated','RolledBack']:
    print(f'  {k:20s} {c.get(k,0)}')
" 2>/dev/null || echo "  (no events file)"

echo ""
echo "=== Validation Lag ==="
[ -f "$EVENTS" ] && python3 -c "
import json, sys
# Use node-0 as reference
r, v = [], []
for line in open('$EVENTS'):
    try:
        e = json.loads(line)
        m, t = e['message'], e['time_s']
        if m.get('node') != 'node-0': continue
        if m['type'] == 'RBReceived': r.append(t)
        elif m['type'] == 'BlockValidated': v.append(t)
    except: pass
print(f'  node-0: received={len(r)} validated={len(v)} pending={len(r)-len(v)}')
if len(v) >= 3:
    gaps = [v[i] - v[i-1] for i in range(-3, 0)]
    print(f'  Last 3 validation intervals: {[round(g, 1) for g in gaps]}s')
" 2>/dev/null || echo "  (no events file)"
