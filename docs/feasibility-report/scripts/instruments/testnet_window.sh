#!/bin/sh
# Run every testnet instrument for one window and write its saved outputs,
# the files the printers (ladder_table.py, stage_table.py, praos_table.py)
# read, into <outputs>/<KEY>/ (or <outputs>/<KEY>/archive-only/ with
# --archive-only, from the SPO archive's period database alone).
#
#   testnet_window.sh KEY DB T0 T1 [--archive-only] [--keep-pairs]
#
#   KEY   f1-high | f2-high | 1kb: names the windows file data/windows/windows-KEY.txt
#   DB    the period database (DATA.md: archive/<KEY>-merged.duckdb, or the
#         archive-only build with --archive-only)
#   T0 T1 the period's bounds, UTC 'YYYY-MM-DD HH:MM:SS'
#   --keep-pairs   keep the per-pair validation file (validation_pairs.csv,
#         tens of MB, the regression's input); by default only its per-node
#         summary is kept
#
# Environment: DATA (the data folder holding chain-2026-10-18/, default the
# parent of this repository), OUTPUTS (default outputs/ in this repository).
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
[ -n "$KEEP" ] || rm -f validation_pairs.csv
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
echo "done: $(ls | tr '\n' ' ')"
