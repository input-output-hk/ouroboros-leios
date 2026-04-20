set -eu

# Usage: churn_loop.sh [db] [n] [x] [churn_percent]
#
#   db             sqlite filename the script creates and churns.
#                  rm -f'd at the start --- don't point at a file you care about.
#                  Default: StartSmall.sqlite
#   n              steady-state EB count the extend step tops up to.
#                  Default: 10000
#   x              number of churn iterations.
#                  Default: 10
#   churn_percent  each iteration prunes EBs whose ebSlot is at or below
#                  this percentile, then extends back up to n.
#                  Default: 10
#
# Outputs (info-*.sql, timings-*.txt, timingsClosures-*.txt) land in $PWD.
# The python scripts are resolved relative to this script, so you can
# cd into any directory and invoke as `bash /path/to/churn_loop.sh ...`.

db=${1:-StartSmall.sqlite}
n=${2:-10000}
x=${3:-10}
churn_percent=${4:-10}

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

function analyses() {
  >"info-$1-$db.sql" sqlite3_analyzer "$db"
  >"timings-$1-$db.txt" python "$here/queryEbBodies.py" "$db"
  >"timingsClosures-$1-$db-only4000.txt" python "$here/queryEbClosures.py" "$db" 4000 8000
}

rm -f "$db" || true

echo -n "======== Extending - 0 / $x - "; date
python "$here/extendDb.py" "$db" "$n"

analyses 0

for i in $(seq "$x"); do
    echo -n "======== Pruning - $i / $x - "; date
    python "$here/pruneDb.py" "$db" "$(sqlite3 "$db" "SELECT percentile(ebSlot, $churn_percent) FROM EB;")"
#    python "$here/pruneDb.py" "$db" "$(sqlite3 "$db" 'SELECT MIN(ebSlot) FROM EB;')"

    echo -n "======== Extending - $i / $x - "; date
    python "$here/extendDb.py" "$db" "$n"

#    if (( 0 == (i % 15) )); then
        analyses "$i"
#    fi
done

echo -n "======== Done - "; date
