#!/usr/bin/env bash
set -euo pipefail
# Usage: demo/scripts/10_init_inputs.sh [-d DEMO_DIR] [--pools 3000] [--stake 100000] [--alpha 5] [--beta 1]
DIR_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$DIR_SCRIPT/.env_cli"

DEMO_DIR="$(cd "$DIR_SCRIPT/.." && pwd)"
POOLS=5000
TOTAL_STAKE=100000
ALPHA=5
BETA=1

while [[ $# -gt 0 ]]; do
  case "$1" in
    -d) DEMO_DIR="$2"; shift 2;;
    --pools) POOLS="$2"; shift 2;;
    --stake) TOTAL_STAKE="$2"; shift 2;;
    --alpha) ALPHA="$2"; shift 2;;
    --beta)  BETA="$2"; shift 2;;
    *) echo "Unknown arg: $1"; exit 2;;
  esac
done

mkdir -p "$DEMO_DIR"

echo "== [10_init_inputs] DIR=${DEMO_DIR} POOLS=${POOLS} TOTAL_STAKE=${TOTAL_STAKE} =="

pushd "$DEMO_DIR" >/dev/null
"$CLI" gen-eid > eid.txt
"$CLI" gen-eb-hash > ebhash.txt

"$CLI" gen-stake \
  --pool-count "${POOLS}" \
  --total-stake "${TOTAL_STAKE}" \
  --shape-alpha "${ALPHA}" \
  --shape-beta "${BETA}" \
  --stake-file stake.cbor

"$CLI" gen-pools \
  --stake-file stake.cbor \
  --pools-file pools.cbor

# Pretty-print some of the generated values
echo "EID: $(cat eid.txt)"
echo "EB Hash: $(cat ebhash.txt)"

# Print first 3 pools and their stakes from pools.cbor using cbor2
PYTHON_EXEC="${VIRTUAL_ENV:+$VIRTUAL_ENV/bin/python}"
PYTHON_EXEC="${PYTHON_EXEC:-python3}"
"$PYTHON_EXEC" - <<'PY'
import sys, os
try:
    import cbor2
except ImportError:
    print('cbor2 not installed! (pip install cbor2)', file=sys.stderr)
    sys.exit(1)

if not os.path.exists('pools.cbor'):
    print('pools.cbor not found', file=sys.stderr)
    sys.exit(1)

with open('pools.cbor', 'rb') as f:
    pools = cbor2.load(f)

print('First 3 pools and their stakes:')
for i, entry in enumerate(pools[:3]):
    # Expected structure: {"secret": <bytes>, "reg": {"pool": "<hex>", ...}, "stake": <int>}
    reg = entry.get('reg', {})
    pool_id = reg.get('pool', '<unknown>')
    stake = entry.get('stake', '<unknown>')
    print(f'  {i:>2}: pool={pool_id}  stake={stake}')
PY
popd >/dev/null

echo "Initialized inputs in ${DEMO_DIR}"