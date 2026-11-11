#!/bin/sh
# Run every testnet instrument for one window and write its saved outputs,
# the files the printers (ladder_table.py, stage_table.py, praos_table.py,
# cost_table.py, diffusion_table.py) read, into <outputs>/<KEY>/ (or
# <outputs>/<KEY>/archive-only/ with --archive-only, from the SPO archive's
# period database alone: the section 4 check column, without the section 5
# and 6 outputs).
#
#   testnet_window.sh KEY DB T0 T1 [--archive-only] [--keep-pairs]
#
#   KEY   f1-high | f2-high | 1kb: names the windows file data/windows/windows-KEY.txt
#   DB    the period database (DATA.md: archive/<KEY>-merged.duckdb, or the
#         archive-only build with --archive-only)
#   T0 T1 the period's bounds, UTC 'YYYY-MM-DD HH:MM:SS'
#   --keep-pairs   keep the per-pair files (validation_pairs.csv, tens of MB,
#         the regression's input; voter_stages_pairs.csv, the per-vote
#         records); by default only their summaries are kept
#
# Environment: DATA (the data folder holding chain-2026-10-18/ and the
# archived monitoring pulls grafana/archive/{loki/peers,mimir}/<KEY>/,
# default the parent of this repository), OUTPUTS (default outputs/ in this
# repository); the hosts table is data/hosts.csv in this repository.
# Needs duckdb and python3 on PATH. The passes over a 30 GB period database
# take minutes each; the whole window about half an hour.
#
#   (from the repository) scripts/instruments/testnet_window.sh f2-high ../archive/f2-high-merged.duckdb '2026-10-24 12:00:00' '2026-10-26 13:00:00'
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
DATA=${DATA:-$(cd "$REPO/.." && pwd)}
OUTPUTS=${OUTPUTS:-$REPO/outputs}
KEY=$1; DB=$(cd "$(dirname "$2")" && pwd)/$(basename "$2"); T0=$3; T1=$4; shift 4
ARCHIVE_ONLY=; KEEP=
for a in "$@"; do case $a in --archive-only) ARCHIVE_ONLY=1;; --keep-pairs) KEEP=1;; *) echo "unknown flag $a" >&2; exit 2;; esac; done
WIN=$REPO/data/windows/windows-$KEY.txt
CHAIN=$DATA/chain-2026-10-18/blocks.sqlite
COMMITTEE=$DATA/chain-2026-10-18/committee.sqlite
SLOT0=1792281600
OUT=$OUTPUTS/$KEY${ARCHIVE_ONLY:+/archive-only}
mkdir -p "$OUT"; cd "$OUT"
V="set variable t0 = '$T0'; set variable t1 = '$T1'; set variable win = '$WIN'; set variable chain = '$CHAIN'; set variable committee = '$COMMITTEE';"
FROM=$(echo "$T0" | tr ' ' T); TO=$(echo "$T1" | tr ' ' T)
# the hours between the loaded windows, excluded from the per-node diffusion tables (start and end of each gap;
# a time written without seconds gets them)
EXCL=$(awk 'function s(t) { return length(t) == 16 ? t ":00" : t }
            !/^#/ && NF==2 {if (prev!="") printf "--exclude %s,%s ", s(prev), s($1); prev=$2}' "$WIN")
TICKERS=$DATA/chain-2026-10-18/tickers.csv

echo "== $KEY -> $OUT"
echo "-- diffusion, closure and body stage"
python3 "$HERE/diffusion_nodes.py" --db "$DB" --from "$FROM" --to "$TO" --chain "$CHAIN" --slot0 $SLOT0 --tickers "$TICKERS" \
    --percentiles 90,95,99 --before 3,4,5,7 --sort p90 $EXCL --out diffusion.md --csv diffusion.csv
python3 "$HERE/diffusion_nodes.py" --db "$DB" --from "$FROM" --to "$TO" --chain "$CHAIN" --slot0 $SLOT0 --tickers "$TICKERS" \
    --percentiles 90,95,99 --before 3,4,5,7 --sort p90 $EXCL --stage body --out diffusion-body.md --csv diffusion-body.csv
echo "-- validation (per-node summary), tally, closure fleet, never-completed closures"
duckdb -readonly -markdown "$DB" -c "$V" -f "$HERE/validation_pairs.sql" > validation.md
if [ -z "$ARCHIVE_ONLY" ]; then
  echo "-- voter stages (8.1): per vote scheduled, where the voter lost the EB, by EB size"
  duckdb -readonly -markdown "$DB" -c "$V" -f "$HERE/voter_stages.sql" > voter_stages.md
  python3 "$HERE/voter_stages.py" voter_stages_pairs.csv --chain "$CHAIN" --csv voter_stages.csv >> voter_stages.md
  echo "-- validation by applied share (6.1) and the per-transaction cost on closures of one size (7), from the per-pair file"
  python3 "$HERE/validation_bins.py" validation_pairs.csv --hosts "$REPO/data/hosts.csv" > validation_bins.md
  # validation by EB size class (4.3.1's prose): closure arrival and validation time per class
  python3 "$HERE/validation_classes.py" validation_pairs.csv > validation_classes.md
  # the per-transaction cost by input provenance (Table 7.2): the EB size class per window, the
  # chained closures (80 % or more of the inputs spend an output of the same block) and the old-input
  # ones (half or less) side by side; eb_shape_dbsync.csv is the saved db-sync composition of the
  # window's certified closures (DATA.md), fetched outside this repository
  case $KEY in
    f1-high) CLASS="--class 1000 1499";;
    f2-high) CLASS="--class 2000 4999";;
    1kb)     CLASS="--class 1500 2499";;
  esac
  SHAPE="validation_pairs.csv --hosts $REPO/data/hosts.csv --shape eb_shape_dbsync.csv --chain $CHAIN"
  python3 "$HERE/validation_shape.py" $SHAPE $CLASS --provenance 0.8 0.5 > validation_shape.md
  if [ "$KEY" = f1-high ]; then
    # the within-kind check read in 7.2's prose: closures of the 247 B transaction alone, by their same-block share
    : > validation_shape_kind.md
    for band in "0 0.1" "0.1 0.5" "0.5 0.8" "0.8 1"; do
      python3 "$HERE/validation_shape.py" $SHAPE $CLASS --min-size 200 --max-size 260 --same-block-min ${band% *} --same-block-max ${band#* } >> validation_shape_kind.md
    done
  fi
  if [ "$KEY" = f2-high ]; then
    # the size series (read in 7.2 and 7.3): chained closures of one transaction size across the EB size classes
    python3 "$HERE/validation_shape.py" $SHAPE --class 1000 1999 --class 2000 2999 --class 3000 3999 --class 5500 6999 \
      --min-size 200 --max-size 260 --same-block-min 0.8 > validation_shape_series.md
  fi
  # the records repriced by host class (Tables 8.3a, 8.3b): per class the cost per applied transaction on old-input
  # closures, on chained closures, and per reapplied transaction, in ms / ms / us. The 2 MB windows take the
  # cluster's c5d old-input reading at 2,500 to 3,000 transactions (Table 7.3, 1.85 ms) scaled by the hardware
  # factors (0.85, 0.6), the chained and reapply costs of Table 7.2b; the 260 kB window its own Table 7.2a
  # readings (the current generation's old-input cost from the c5d reading and the hardware factor)
  case $KEY in
    f1-high) COSTS=("current:0.50:0.19:88" "two older:0.75:0.30:135" "three older:0.83:0.35:140");;
    *)       COSTS=("current:1.11:0.20:85" "two older:1.57:0.31:128" "three older:1.85:0.35:147");;
  esac
  python3 "$HERE/testnet_speed.py" validation_pairs.csv --voters voters.csv --windows "$WIN" --ebs tally_quorum_ebs.csv \
    --hosts "$REPO/data/hosts.csv" --ladder ladder.jsonl --fleet closure_fleet_per_eb.csv --costs "${COSTS[@]}" > host_speed.md
  # the votes repriced (Tables 8.3a to 8.3c): the same rows read per vote on the per-vote records, no certification projected
  python3 "$HERE/voter_reprice.py" voter_stages_pairs.csv --hosts "$REPO/data/hosts.csv" --costs "${COSTS[@]}" > voter_reprice.md
fi
[ -n "$KEEP" ] || rm -f validation_pairs.csv voter_stages_pairs.csv
duckdb -readonly -markdown "$DB" -c "$V" -f "$HERE/tally_quorum.sql" > tally.md
duckdb -readonly -markdown "$DB" -c "$V" -f "$HERE/closure_fleet.sql" > closure_fleet.md
if [ -z "$ARCHIVE_ONLY" ]; then
  duckdb -readonly -markdown "$DB" -c "$V" -f "$HERE/closure_never.sql" > closure_never.md
  echo "-- Praos side: adoption delay, consecutive-slot pairs, adoption path"
  duckdb -readonly -markdown "$DB" -c "$V" -f "$HERE/adoption_delay.sql" > adoption.md
  duckdb -readonly -markdown "$DB" -c "$V" -f "$HERE/consecutive_pairs.sql" > pairs.md
  duckdb -readonly -markdown "$DB" -c "$V" -f "$HERE/adoption_path.sql" > adoption_path.md
  echo "-- ladder and sizes (chain alone)"
  python3 "$HERE/ladder.py" ceiling --chain "$CHAIN" --committee "$COMMITTEE" --windows "$WIN" --gap 14 --rb-bytes 90112 --export ladder.jsonl > ladder.md
  python3 "$HERE/ladder.py" sizes --chain "$CHAIN" --windows "$WIN" --gap 14 > sizes.md
  if [ "$KEY" = f2-high ]; then
    echo "-- forge path (the 2 MB period's archived call traces)"
    python3 "$HERE/forge_path.py" --data "$DATA" --win "$WIN" > forge_path.md
  fi
fi
echo "-- reporting coverage"
duckdb -readonly -markdown "$DB" -c "$V" -f "$HERE/coverage.sql" > coverage.md
if [ -z "$ARCHIVE_ONLY" ]; then
  echo "-- the hosts' upstream peers, the diffusion bins and upstream groups (section 6.3)"
  python3 "$HERE/peers_upstream.py" "$DATA/grafana/archive/loki/peers/$KEY" "$FROM" "$TO" > upstream_hosts.csv
  python3 "$HERE/diffusion_bins.py" .
  echo "-- memory and CPU (section 6.4)"
  python3 "$HERE/resources.py" testnet --db "$DB" --t0 "$T0" --t1 "$T1" --mimir "$DATA/grafana/archive/mimir/$KEY" --hosts "$REPO/data/hosts.csv" > resources.md
fi
echo "done: $(ls | tr '\n' ' ')"
