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
echo "-- voter stages (8.1): per announcement accepted, where the node lost the EB, by EB size (the w42 build has no vote-scheduled or body-hits event)"
printf '%s %s\n' "$T0" "$T1" > voter_stages_window.txt
duckdb -readonly -markdown cluster.duckdb -c "set variable t0 = '$T0'; set variable t1 = '$T1'; set variable win = 'voter_stages_window.txt'; set variable slot0 = $SLOT0; set variable sched_ns = 'Consensus.LeiosKernel.AnnouncementAccepted';" \
    -f "$HERE/voter_stages.sql" > "$OUT/voter_stages.md"
python3 "$HERE/voter_stages.py" voter_stages_pairs.csv --chain blocks.sqlite --gap "$GAP" --csv "$OUT/voter_stages.csv" >> "$OUT/voter_stages.md"
rm -f voter_stages_pairs.csv voter_stages_window.txt
echo "-- Praos side: adoption delay and leadership, forks, adoption path"
# these three attach the run's files read-only into an in-memory database (no -readonly flag: it refuses an in-memory database)
duckdb -markdown -f "$HERE/cluster_adoption.sql" > "$OUT/adoption.md"
duckdb -markdown -f "$HERE/cluster_forks.sql" > "$OUT/pairs.md"
duckdb -markdown -f "$HERE/cluster_adoption_path.sql" > "$OUT/adoption_path.md"
echo "-- ladder and sizes (chain alone)"
python3 "$HERE/ladder.py" ceiling --chain blocks.sqlite --from "$T0" --to "$T1" --all --gap "$GAP" --ref-cap "$REF" --payload-cap "$PAY" --rb-bytes 90112 --export "$OUT/ladder.jsonl" > "$OUT/ladder.md"
python3 "$HERE/ladder.py" sizes --chain blocks.sqlite --from "$T0" --to "$T1" --gap "$GAP" > "$OUT/sizes.md"
echo "-- validation by applied share, the per-transaction cost on the modal EB class, the host-speed counterfactual (sections 6.1, 7, 8 and 6.2)"
python3 "$HERE/validation_bins.py" validation_pairs.csv > "$OUT/validation_bins.md"
python3 "$HERE/validation_shape.py" validation_pairs.csv > "$OUT/validation_shape.md"
# the size series (Table 7.3): the same readings per 500-transaction class, the classes the run populates
python3 "$HERE/validation_shape.py" validation_pairs.csv --class 1000 1499 --class 1500 1999 --class 2000 2499 --class 2500 2999 > "$OUT/validation_shape_series.md"
# the records repriced on faster hosts and with the loop's cost removed (Table 8.4): the run's costs per applied and reapplied
# transaction (Table 7.3), the hardware factors of Table 7.2 (c6id 0.85, current 0.6 of c5d on both
# operations) and the loop fix (apply at the c5d hosts' chained cost of Table 7.2b, 0.35 ms, reapply unchanged)
case $KEY in
  cluster-40k260k)     COSTS="0.91 152"; FIX=0.38;;
  cluster-100k1m)      COSTS="1.85 144"; FIX=0.19;;
  cluster-100k1m-374)  COSTS="3.42 163"; FIX=0.19;;
esac
python3 "$HERE/host_speed.py" validation_pairs.csv "$OUT/ladder.jsonl" "$E_KB" --costs $COSTS "as measured:1:1" \
  "hosts two generations newer (c6id):0.85:0.85" "hosts of the current generation:0.6:0.6" \
  "the loop's cost removed, on the run hosts:$FIX:1" "validation started at the closure arrival:1:1:closure" > "$OUT/host_speed.md"
if [ "$KEY" = cluster-100k1m ]; then
  # the loop fix combined with each host generation's measured costs (Table 8.5): apply at the class's chained
  # cost and reapply at its cost (Table 7.2b: 0.35/147, 0.31/128, 0.20/85) relative to the run's 1.85 ms / 144 us
  python3 "$HERE/host_speed.py" validation_pairs.csv "$OUT/ladder.jsonl" "$E_KB" --costs $COSTS "as measured:1:1" \
    "the loop's cost removed, on the run c5d hosts:0.189:1.0" "the loop's cost removed, on c6id hosts:0.168:0.889" \
    "the loop's cost removed, on current-generation hosts:0.108:0.590" > "$OUT/host_speed_combined.md"
fi
echo "-- diffusion bins and upstream groups (6.3), memory and CPU (6.4)"
python3 "$HERE/diffusion_bins.py" "$OUT"
python3 "$HERE/resources.py" cluster --resources raw/Resources.db > "$OUT/resources.md"
echo "done: $(ls "$OUT" | tr '\n' ' ')"
