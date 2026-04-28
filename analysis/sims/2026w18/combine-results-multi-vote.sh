#!/usr/bin/env nix-shell
#!nix-shell -i bash -p gnused gzip pigz "rWrapper.override { packages = with rPackages; [ data_table R_utils bit64 ggplot2 magrittr stringr ]; }"

set -e

usage() {
  cat <<'USAGE'
Usage: combine-results-multi-vote.sh -m MODE [-s SEED] [--topology NAME]

Combine experiment results from a specific voting mode, topology, and seed.

Options:
  -m, --voting-mode MODE   wfa-ls | everyone | top-stake-fraction
  -s, --seed N             RNG seed (default: 0)
  --topology NAME          Topology subdirectory (default: topology-v2)
  -h, --help               Show this help
USAGE
  exit "${1:-0}"
}

MODE=""
SEED=0
TOPOLOGY=topology-v2
while [[ $# -gt 0 ]]; do
  case "$1" in
    -m|--voting-mode) MODE="$2"; shift 2 ;;
    -s|--seed)        SEED="$2"; shift 2 ;;
    --topology)       TOPOLOGY="$2"; shift 2 ;;
    -h|--help)        usage 0 ;;
    *)                echo "ERROR: unknown option '$1'" >&2; usage 1 ;;
  esac
done

if [[ -z "$MODE" ]]; then
  echo "ERROR: -m/--voting-mode is required" >&2
  usage 1
fi

case "$MODE" in
  wfa-ls|everyone|top-stake-fraction) ;;
  *) echo "ERROR: unknown voting mode '$MODE'" >&2; usage 1 ;;
esac

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EXPERIMENTS=(
  # NA experiments — varying throughput, no Plutus
  NA,0.150
  NA,0.200
  NA,0.250
  NA,0.300
  NA,0.350
  # Plutus experiments — fixed 0.250 TxMB/s, varying Plutus CPU load
  1000,0.250
  2000,0.250
  5000,0.250
  10000,0.250
  20000,0.250
  50000,0.250
)

mkdir -p "results/$MODE/$TOPOLOGY"

for f in lifecycle resources receipts cpus sizes
do
  # Find first non-empty result to get headers
  FIRST=""
  for exp in "${EXPERIMENTS[@]}"; do
    g="$SCRIPT_DIR/experiments/$exp/$MODE/$TOPOLOGY/seed-$SEED"
    if [ -f "$g/$f.csv.gz" ] && [ -s "$g/$f.csv.gz" ]; then
      FIRST="$g"
      break
    fi
  done
  if [ -z "$FIRST" ]; then
    echo "No $f.csv.gz found for mode $MODE, skipping" >&2
    continue
  fi

  HL=$(sed -n -e '1p' "$FIRST/case.csv")
  HR=$(zcat "$FIRST/$f.csv.gz" | sed -n -e '1p')
  if [[ "$f" == "lifecycle" || "$f" == "resources" || "$f" == "sizes" ]]
  then
    FRACT=1.00
  else
    FRACT=0.15
  fi
  (
    echo "$HL,$HR"
    for exp in "${EXPERIMENTS[@]}"; do
      g="$SCRIPT_DIR/experiments/$exp/$MODE/$TOPOLOGY/seed-$SEED"
      if [ ! -d "$g" ]; then
        echo "Skipping $exp/$MODE: directory not found" >&2
        continue
      fi
      if [ ! -e "$g/stderr" ]; then
        echo "Skipping $exp/$MODE: no stderr" >&2
        continue
      fi
      if [ -s "$g/stderr" ]; then
        echo "Skipping $exp/$MODE: stderr not empty" >&2
        continue
      fi
      if [ ! -f "$g/$f.csv.gz" ] || [ ! -s "$g/$f.csv.gz" ]; then
        echo "Skipping $exp/$MODE: $f.csv.gz missing or empty" >&2
        continue
      fi
      BL=$(sed -n -e '2p' "$g/case.csv")
      zcat "$g/$f.csv.gz" | gawk 'FNR > 1 && rand() <= '"$FRACT"' { print "'"$BL"'" "," $0}'
    done
  ) | pigz -p 3 -9c > results/$MODE/$TOPOLOGY/$f.csv.gz
R --vanilla << EOI > /dev/null
require(data.table)
sampleSize <- $FRACT
print(sampleSize)
$f <- fread("results/$MODE/$TOPOLOGY/$f.csv.gz", stringsAsFactors=TRUE)
# When all experiments have empty Plutus, fread infers column as logical NA;
# coerce to factor with "" level so downstream factor() comparisons work.
if ("Plutus" %in% names($f) && (is.logical($f\$Plutus) || all(is.na($f\$Plutus)))) {
  $f[, Plutus := NULL]
  $f[, Plutus := factor(rep("", .N), levels="")]
}
save($f, sampleSize, file="results/$MODE/$TOPOLOGY/$f.Rdata", compression_level=9)
EOI
done
