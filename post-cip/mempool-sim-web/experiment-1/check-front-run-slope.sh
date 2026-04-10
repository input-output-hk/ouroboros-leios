#!/usr/bin/env bash

set -euo pipefail

if [ "$#" -lt 2 ] || [ "$#" -gt 4 ]
then
  echo "Usage: $0 <adversaries.tsv.gz> <rb|total> [min_slope] [max_slope]" >&2
  exit 1
fi

TSV_GZ=$1
MODE=$2
MIN_SLOPE=${3:-}
MAX_SLOPE=${4:-}

if [ ! -f "$TSV_GZ" ]
then
  echo "Input file '$TSV_GZ' not found." >&2
  exit 1
fi

if [ "$MODE" != "rb" ] && [ "$MODE" != "total" ]
then
  echo "Mode must be 'rb' or 'total'." >&2
  exit 1
fi

SLOPE=$(
  zcat "$TSV_GZ" \
  | awk -F'\t' -v mode="$MODE" '
      NR == 1 { next }
      {
        adv = $1 + 0
        rbh[adv] += $3 + 0
        rba[adv] += $4 + 0
        ebh[adv] += $6 + 0
        eba[adv] += $7 + 0
      }
      END {
        for (a in rbh) {
          rb_t = rbh[a] + rba[a]
          tot_t = rb_t + ebh[a] + eba[a]
          if (mode == "rb") {
            if (rb_t == 0) continue
            y = 100 * rba[a] / rb_t
          } else {
            if (tot_t == 0) continue
            y = 100 * (rba[a] + eba[a]) / tot_t
          }
          x = 100 * a / (10000 + a)
          n++
          sx += x
          sy += y
          sxx += x * x
          sxy += x * y
        }
        denom = n * sxx - sx * sx
        if (n < 2 || denom == 0) {
          print "nan"
          exit 0
        }
        b = (n * sxy - sx * sy) / denom
        printf "%.9f\n", b
      }
    '
)

if [ "$SLOPE" = "nan" ]
then
  echo "Unable to compute slope (insufficient data)." >&2
  exit 1
fi

echo "mode=$MODE slope=$SLOPE file=$TSV_GZ"

if [ -n "$MIN_SLOPE" ]
then
  awk -v x="$SLOPE" -v min="$MIN_SLOPE" 'BEGIN { exit !(x >= min) }' \
    || { echo "Slope $SLOPE is below minimum $MIN_SLOPE." >&2; exit 1; }
fi

if [ -n "$MAX_SLOPE" ]
then
  awk -v x="$SLOPE" -v max="$MAX_SLOPE" 'BEGIN { exit !(x <= max) }' \
    || { echo "Slope $SLOPE is above maximum $MAX_SLOPE." >&2; exit 1; }
fi
