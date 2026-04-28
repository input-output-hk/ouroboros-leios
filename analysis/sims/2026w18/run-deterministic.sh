#!/usr/bin/env nix-shell
#!nix-shell -i bash -p ansifilter gnugrep gnused gzip pigz bc

set -eo pipefail

usage() {
  cat <<'USAGE'
Usage: run-deterministic.sh [options]

Run a deterministic turbo-mode simulation in the current experiment directory.

Options:
  -m, --voting-mode MODE   wfa-ls | everyone | top-stake-fraction (default: wfa-ls)
  -s, --seed N             RNG seed (default: 0)
  --memory-limit           Apply backlog memory limits (uses memory-limit.yaml)
  --memory-limit-file PATH Use a specific memory-limit YAML (relative to
                           sim-rs/parameters/, e.g. memory-limit-safe.yaml)
  --actor                  Use actor engine (async, non-deterministic)
  --sequential             Use sequential DES engine (deterministic, single shard)
  --turbo                  Use turbo mode (default: sequential, 6-shard zero-latency-clusters)
  --quorum-fraction FRAC   Quorum fraction for vote threshold (default: 0.75)
  --stake-fraction FRAC    Stake fraction for top-stake-fraction mode (default: 0.99)
  --topology NAME          Topology file basename in data/simulation/pseudo-mainnet/
                           (default: topology-v2; e.g. topology-v2-1500 for 1500 nodes)
  -h, --help               Show this help
USAGE
  exit "${1:-0}"
}

# Defaults
SEED=0
VOTING_MODE=wfa-ls
QUORUM_FRACTION=0.75
STAKE_FRACTION=0.99
USE_MEMORY_LIMIT=false
MEMORY_LIMIT_FILE=memory-limit.yaml
ENGINE=turbo
NETWORK=topology-v2

while [[ $# -gt 0 ]]; do
  case "$1" in
    -m|--voting-mode)     VOTING_MODE="$2"; shift 2 ;;
    -s|--seed)            SEED="$2"; shift 2 ;;
    --memory-limit)       USE_MEMORY_LIMIT=true; shift ;;
    --memory-limit-file)  USE_MEMORY_LIMIT=true; MEMORY_LIMIT_FILE="$2"; shift 2 ;;
    --actor)              ENGINE=actor; shift ;;
    --sequential)         ENGINE=sequential; shift ;;
    --turbo)              ENGINE=turbo; shift ;;
    --quorum-fraction)    QUORUM_FRACTION="$2"; shift 2 ;;
    --stake-fraction)     STAKE_FRACTION="$2"; shift 2 ;;
    --topology)           NETWORK="$2"; shift 2 ;;
    -h|--help)            usage 0 ;;
    *)                    echo "ERROR: unknown option '$1'" >&2; usage 1 ;;
  esac
done

TX_START=60
TX_STOP=960
SIM_STOP=1500
BW=10
CPU_COUNT=4
VARIANT=linear-with-tx-references
BLOCK_SIZE=12
TX_SIZE=1500
LABEL=$(basename "$PWD")
PROPAGATION=eb-received
STAGE_LENGTH_DIFF=7
STAGE_LENGTH_VOTE=4
PLUTUS=$(echo -n "$LABEL" | sed -e 's/^\(.*\),\(.*\)/\1/')
THROUGHPUT=$(echo -n "$LABEL" | sed -e 's/^\(.*\),\(.*\)/\2/')
TX_SPACING_HONEST=$(echo "scale=3; $TX_SIZE / $THROUGHPUT / 1000" | bc)

# Deterministic turbo mode: sequential DES with sharded parallelism
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$SCRIPT_DIR/../../.."
PARAMS_DIR="$REPO_ROOT/sim-rs/parameters"
TURBO="$PARAMS_DIR/turbo.yaml"
TOPO_SOURCE="$REPO_ROOT/data/simulation/pseudo-mainnet/$NETWORK.yaml"

ulimit -S -m 96000000 -v 96000000

if [[ -e sim.log ]]
then
  rm sim.log
fi

mkfifo sim.log

# Create output subdirectory up front (before config generation)
OUTDIR="$VOTING_MODE/$NETWORK/seed-$SEED"
mkdir -p "$OUTDIR"

sed -e 's/"bandwidth-bytes-per-second":125000000/"bandwidth-bytes-per-second":'"$((125000 * BW))"'/g' \
    -e 's/"cpu-core-count":6,/"cpu-core-count":'"$CPU_COUNT"',/g' \
    "$TOPO_SOURCE" > network.yaml

yaml2json ../config.yaml \
| jq '. +
{
  "leios-variant": "'"$VARIANT"'"
, "linear-eb-propagation-criteria": "'"$PROPAGATION"'"
, "linear-diffuse-stage-length-slots": '"$STAGE_LENGTH_DIFF"'
, "linear-vote-stage-length-slots": '"$STAGE_LENGTH_VOTE"'
, "leios-stage-length-slots": '"$STAGE_LENGTH_VOTE"'
, "eb-referenced-txs-max-size-bytes": ('"$BLOCK_SIZE"' * 1000000)
, "eb-body-avg-size-bytes": ('"$BLOCK_SIZE"' * 1000000)
, "tx-size-bytes-distribution": {distribution: "constant", value: '"$TX_SIZE"'}
, "tx-generation-distribution": {distribution: "constant", value: '"$TX_SPACING_HONEST"'}
, "tx-start-time": '"$TX_START"'
, "tx-stop-time": '"$TX_STOP"'
} + (
  if "'"$PLUTUS"'" == "NA"
  then
    {}
  else
    {
      "tx-validation-cpu-time-ms": (0.2624 + ("'"$PLUTUS"'" | tonumber) * 0.05 / '"$THROUGHPUT"' / 1000000 * '"$TX_SIZE"' * 0.9487)
    , "rb-body-legacy-praos-payload-validation-cpu-time-ms-constant": (0.3478 + 20 * 0.02127)
    , "rb-body-legacy-praos-payload-validation-cpu-time-ms-per-byte": 0.00001943
    , "eb-body-validation-cpu-time-ms-constant": (0.3478 + (("'"$PLUTUS"'" | tonumber) - 20) * 0.02127)
    , "eb-body-validation-cpu-time-ms-per-byte": 0.00001943
    }
  end
)
' > "$OUTDIR/config.yaml"

# Seed override for deterministic runs
echo "seed: $SEED" > seed.yaml

# Compute vote threshold from topology and generate voting override
read -r TOTAL_NODES STAKING_NODES TOP_STAKE_NODES < <(python3 -c "
import json, yaml, sys
with open('$TOPO_SOURCE') as f:
    first = f.read(1); f.seek(0)
    d = json.load(f) if first == '{' else yaml.safe_load(f)
nodes = d['nodes']
if isinstance(nodes, dict):
    stakes = [n.get('stake', 0) for n in nodes.values()]
else:
    stakes = [n.get('stake', 0) for n in nodes]
total_nodes = len(stakes)
staking = sorted([s for s in stakes if s > 0], reverse=True)
total_stake = sum(staking)
threshold = total_stake * $STAKE_FRACTION
cum = 0
top_n = 0
for s in staking:
    if cum >= threshold: break
    cum += s
    top_n += 1
print(total_nodes, len(staking), top_n)
")

case "$VOTING_MODE" in
  wfa-ls)
    VOTE_THRESHOLD=450
    cat > voting.yaml <<EOF
committee-selection-algorithm: "wfa-ls"
vote-threshold: $VOTE_THRESHOLD
persistent-vote-generation-probability: 480
non-persistent-vote-generation-probability: 120
EOF
    ;;
  everyone)
    VOTE_THRESHOLD=$(python3 -c "import math; print(math.ceil($TOTAL_NODES * $QUORUM_FRACTION))")
    cat > voting.yaml <<EOF
committee-selection-algorithm: "everyone"
vote-threshold: $VOTE_THRESHOLD
EOF
    ;;
  top-stake-fraction)
    VOTE_THRESHOLD=$(python3 -c "import math; print(math.ceil($TOP_STAKE_NODES * $QUORUM_FRACTION))")
    cat > voting.yaml <<EOF
committee-selection-algorithm: "top-stake-fraction"
vote-threshold: $VOTE_THRESHOLD
committee-stake-fraction-threshold: $STAKE_FRACTION
EOF
    ;;
  *)
    echo "ERROR: unknown voting mode '$VOTING_MODE' (expected wfa-ls, everyone, top-stake-fraction)" >&2
    exit 1
    ;;
esac

echo "Voting mode: $VOTING_MODE (threshold: $VOTE_THRESHOLD)" >&2

CLEANUP_FILES=(sim.log network.yaml seed.yaml voting.yaml engine.yaml)

# Build sim-cli parameter chain; config.yaml goes directly into OUTDIR
SIM_PARAMS=(-p "$OUTDIR/config.yaml")
case "$ENGINE" in
  actor)
    echo "Engine: actor (async)" >&2
    ;;
  sequential)
    cat > engine.yaml <<EOF
engine: sequential
shard-count: 1
EOF
    SIM_PARAMS+=(-p engine.yaml)
    echo "Engine: sequential (single shard)" >&2
    ;;
  turbo)
    SIM_PARAMS+=(-p "$TURBO")
    echo "Engine: turbo (6-shard zero-latency-clusters)" >&2
    ;;
esac
SIM_PARAMS+=(-p voting.yaml)
if [[ "$USE_MEMORY_LIMIT" == "true" ]]; then
  SIM_PARAMS+=(-p "$PARAMS_DIR/$MEMORY_LIMIT_FILE")
  echo "Memory limits: $MEMORY_LIMIT_FILE" >&2
else
  echo "Memory limits: disabled" >&2
fi
SIM_PARAMS+=(-p seed.yaml)

function cleanup() {
  for f in "${CLEANUP_FILES[@]}"; do
    rm -f "$f"
  done
}
trap cleanup EXIT

grep -E -v '(Slot|CpuTask|Lottery)' sim.log | pigz -p 3 -1c > "$OUTDIR/sim.log.gz" &

/usr/bin/time -v -o "$OUTDIR/time.txt" ../../sim-cli "${SIM_PARAMS[@]}" network.yaml --slots "$SIM_STOP" --conformance-events sim.log > "$OUTDIR/stdout" 2> "$OUTDIR/stderr"

wait

if [[ "$PLUTUS" == "NA" ]]
then
cat << EOI > "$OUTDIR/case.csv"
Network,Bandwidth,CPU,Diffusion duration,Voting duration,Max EB size,Tx size,Throughput,Plutus,Tx start [s],Tx stop [s],Sim stop [s]
$NETWORK,$BW Mb/s,$CPU_COUNT vCPU/node,L_diff = $STAGE_LENGTH_DIFF slots,L_vote = $STAGE_LENGTH_VOTE slots,$BLOCK_SIZE MB/EB,$TX_SIZE B/Tx,$THROUGHPUT TxMB/s,,$TX_START,$TX_STOP,$SIM_STOP
EOI
else
cat << EOI > "$OUTDIR/case.csv"
Network,Bandwidth,CPU,Diffusion duration,Voting duration,Max EB size,Tx size,Throughput,Plutus,Tx start [s],Tx stop [s],Sim stop [s]
$NETWORK,$BW Mb/s,$CPU_COUNT vCPU/node,L_diff = $STAGE_LENGTH_DIFF slots,L_vote = $STAGE_LENGTH_VOTE slots,$BLOCK_SIZE MB/EB,$TX_SIZE B/Tx,$THROUGHPUT TxMB/s,$PLUTUS Gstep/EB,$TX_START,$TX_STOP,$SIM_STOP
EOI
fi

zcat "$OUTDIR/sim.log.gz" \
| ../../leios-trace-processor \
  +RTS -N5 -RTS \
  --trace-file /dev/stdin \
  --lifecycle-file "$OUTDIR/lifecycle.csv" \
  --cpu-file "$OUTDIR/cpus.csv" \
  --resource-file "$OUTDIR/resources.csv" \
  --receipt-file "$OUTDIR/receipts.csv"

(
  echo 'Kind,Item,Generated [s],Transactions,Endorses'
  zcat "$OUTDIR/sim.log.gz" \
  | grep -E '(EB|RB)Generated' \
  | jq -r '
    .message.type[0:2]
    + "," + .message.id
    + "," + (.time_s | tostring)
    + "," + (.message.transactions | length | tostring)
    + "," + (if .message.endorsement then .message.endorsement.eb.id else "NA" end)
  '
) > "$OUTDIR/sizes.csv"

pigz -p 3 -9f "$OUTDIR"/{cpus,lifecycle,receipts,resources,sizes}.csv

cat "$OUTDIR/case.csv"

ansifilter "$OUTDIR/stdout" | grep -E '^ INFO (praos|leios|network): ' > "$OUTDIR/summary.txt"

# Marker that the full pipeline completed; combine-results checks for this.
touch "$OUTDIR/done"

echo "Outputs saved to $OUTDIR/" >&2
