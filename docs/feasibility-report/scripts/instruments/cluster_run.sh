#!/bin/sh
# Run every cluster instrument for one run and write its saved outputs, the
# files the printers read, into <outputs>/<KEY>/.
#
#   cluster_run.sh KEY RUN T0 T1 GAP REF_CAP PAYLOAD_CAP E_KB
#
#   KEY     cluster-40k260k | cluster-100k1m | cluster-100k1m-374 (the printers' keys)
#   RUN     the run folder holding the built inputs (DATA.md): cluster.duckdb,
#           blocks.sqlite and raw/*.db
#   T0 T1   the range read, UTC 'YYYY-MM-DDTHH:MM:SS' (the generator's start to
#           the end of the traces, as in the run's ladder export)
#   GAP     the certification gap in slots (15 on the 2026-10-17 run, 14 after)
#   REF_CAP PAYLOAD_CAP   the run's caps in bytes (from its name: 40000 260000, 100000 1000000)
#   E_KB    the run's typical certified closure in kB for the host-speed
#           counterfactual (the median certified closure of sizes.md: 222, 555, 1000)
#
# Environment: OUTPUTS (default outputs/ in this repository). The SQL
# instruments attach the run's files by relative name, so they run from the
# run folder; the per-pair validation file is left there.
#
#   (from the repository) scripts/instruments/cluster_run.sh cluster-100k1m ../cluster/2026-10-20-20-42-... 2026-10-20T21:00:00 2026-10-21T14:47:00 14 100000 1000000 555
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
OUTPUTS=${OUTPUTS:-$REPO/outputs}
KEY=$1; RUN=$(cd "$2" && pwd); T0=$3; T1=$4; GAP=$5; REF=$6; PAY=$7; E_KB=$8
OUT=$OUTPUTS/$KEY
mkdir -p "$OUT"
cd "$RUN"
SLOT0=$(sqlite3 blocks.sqlite "select min(cast(strftime('%s', time) as integer) - slot_no) from block where slot_no is not null")
echo "== $KEY ($RUN, slot 0 = $SLOT0) -> $OUT"
echo "-- diffusion, closure and body stage"
python3 "$HERE/diffusion_nodes.py" --db cluster.duckdb --chain blocks.sqlite --slot0 "$SLOT0" --from "$T0" --to "$T1" \
    --percentiles 50,90,95,99 --before 3,4,5,7 --sort p90 --out "$OUT/diffusion.md" --csv "$OUT/diffusion.csv"
python3 "$HERE/diffusion_nodes.py" --db cluster.duckdb --chain blocks.sqlite --slot0 "$SLOT0" --from "$T0" --to "$T1" \
    --percentiles 50,90,95,99 --before 3,4,5,7 --sort p90 --stage body --out "$OUT/diffusion-body.md" --csv "$OUT/diffusion-body.csv"
echo "-- validation (per-node summary), tally"
duckdb -readonly -markdown cluster.duckdb -f "$HERE/cluster_validation_pairs.sql" > "$OUT/validation.md"
mv validation_nodes.csv "$OUT/"
duckdb -readonly -markdown cluster.duckdb -c "set variable gap = $GAP;" -f "$HERE/cluster_tally_quorum.sql" > "$OUT/tally.md"
mv tally_quorum_nodes.csv tally_quorum_ebs.csv "$OUT/"
echo "-- Praos side: adoption delay and leadership, forks, adoption path"
# these three attach the run's files read-only into an in-memory database (no -readonly flag: it refuses an in-memory database)
duckdb -markdown -f "$HERE/cluster_adoption.sql" > "$OUT/adoption.md"
duckdb -markdown -f "$HERE/cluster_forks.sql" > "$OUT/pairs.md"
duckdb -markdown -f "$HERE/cluster_adoption_path.sql" > "$OUT/adoption_path.md"
echo "-- ladder and sizes (chain alone)"
python3 "$HERE/ladder.py" ceiling --chain blocks.sqlite --from "$T0" --to "$T1" --all --gap "$GAP" --ref-cap "$REF" --payload-cap "$PAY" --rb-bytes 90112 --export "$OUT/ladder.jsonl" > "$OUT/ladder.md"
python3 "$HERE/ladder.py" sizes --chain blocks.sqlite --from "$T0" --to "$T1" --gap "$GAP" > "$OUT/sizes.md"
echo "-- validation by unseen share, the fit, the host-speed counterfactual (sections 6.1, 7, 8 and 6.2)"
python3 "$HERE/validation_bins.py" validation_pairs.csv > "$OUT/validation_bins.md"
python3 "$HERE/validation_fit.py" validation_pairs.csv > "$OUT/validation_fit.md"
python3 "$HERE/host_speed.py" validation_pairs.csv "$OUT/ladder.jsonl" "$E_KB" > "$OUT/host_speed.md"
echo "-- diffusion bins and upstream groups (6.3), memory and CPU (6.4)"
python3 "$HERE/diffusion_bins.py" "$OUT"
python3 "$HERE/resources.py" cluster --resources raw/Resources.db > "$OUT/resources.md"
echo "done: $(ls "$OUT" | tr '\n' ' ')"
