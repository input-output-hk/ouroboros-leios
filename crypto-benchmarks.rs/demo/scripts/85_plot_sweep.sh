#!/usr/bin/env bash
set -euo pipefail
# Plot compression ratios from a sweep run.
# Usage:
#   scripts/85_plot_sweep.sh -d DIR [--open]
# Where:
#   DIR is the sweep directory under demo/ that contains sweep_results.csv
#
# This script prefers demo/scripts/90_plot_sweep.py if present.
# If not, it falls back to a built-in Python snippet.

DIR_SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEMO_ROOT="$(cd "$DIR_SCRIPT/.." && pwd)"

BASE_DIR=""
DO_OPEN=0

usage() {
  cat <<USAGE
Usage: $0 -d DIR [--open]
  -d, --dir   Sweep directory under demo/ (e.g., sweep1)
  --open      (macOS) Open the generated PNG after plotting
USAGE
}

# ---- arg parsing ----
while [[ $# -gt 0 ]]; do
  case "$1" in
    -d|--dir) BASE_DIR="$2"; shift 2;;
    --open) DO_OPEN=1; shift;;
    -h|--help) usage; exit 0;;
    *) echo "Unknown arg: $1" >&2; usage; exit 2;;
  esac
done

[[ -z "$BASE_DIR" ]] && { echo "Error: need -d DIR"; usage; exit 2; }

SWEEP_DIR="${DEMO_ROOT}/${BASE_DIR}"
CSV_PATH="${SWEEP_DIR}/sweep_results.csv"
PNG_PATH="${SWEEP_DIR}/summary_vs_N.png"

if [[ ! -f "$CSV_PATH" ]]; then
  echo "sweep_results.csv not found at: $CSV_PATH"
  echo "Run scripts/80_sweep.sh first."
  exit 1
fi

# Choose Python
PY_BIN="${DEMO_ROOT}/.venv/bin/python"
[[ -x "$PY_BIN" ]] || PY_BIN="python3"

# Ensure matplotlib (install into venv if possible)
if ! "$PY_BIN" -c "import matplotlib" >/dev/null 2>&1; then
  echo "matplotlib not found; attempting install..."
  if [[ -x "${DEMO_ROOT}/.venv/bin/pip" ]]; then
    "${DEMO_ROOT}/.venv/bin/pip" install --upgrade pip matplotlib >/dev/null
  else
    "$PY_BIN" -m pip install --user --upgrade pip matplotlib >/dev/null || true
  fi
fi

# Always use the inline fallback Python to ensure consistent styling/labels.
DEMO_ROOT_OVERRIDE="${DEMO_ROOT}" \
"$PY_BIN" - "${BASE_DIR}" <<'PYFALLBACK'
import sys, csv, os
import matplotlib.pyplot as plt

# argv[1] = base dir under demo/ (e.g., "sweep1")
if len(sys.argv) < 2:
    sys.exit("Usage: fallback: python - <DIR>")
base_dir = sys.argv[1]

# We rely on DEMO_ROOT_OVERRIDE passed from the shell
demo_root = os.environ.get('DEMO_ROOT_OVERRIDE')
if not demo_root:
    raise SystemExit("DEMO_ROOT_OVERRIDE not set; cannot resolve demo path.")

base = os.path.join(demo_root, base_dir)
csv_path = os.path.join(base, 'sweep_results.csv')
png_path = os.path.join(base, 'summary_vs_N.png')

if not os.path.exists(csv_path):
    raise SystemExit(f"sweep_results.csv not found at: {csv_path}")

N = []
ratio = []
pv = []   # persistent_voters_count
npv = []  # nonpersistent_voters_count

with open(csv_path, newline='') as f:
    rdr = csv.DictReader(f)
    for row in rdr:
        try:
            N.append(int(row['N']))
            ratio.append(float(row.get('compression_ratio', 'nan')))
            pv.append(int(row.get('persistent_voters_count', 0)))
            npv.append(int(row.get('nonpersistent_voters_count', 0)))
        except Exception:
            pass

pairs = sorted(zip(N, ratio, pv, npv), key=lambda x: x[0])
if pairs:
    N, ratio, pv, npv = zip(*pairs)
else:
    N, ratio, pv, npv = [], [], [], []

# ---- Build clean x-ticks to avoid clutter and hide 64 explicitly ----
# Strategy:
#   * Always show the first and last N
#   * Prefer showing {32, 128, 256, 512, 1024, 2056, 3000} if present (skip 64)
#   * Fill remaining slots up to ~8 labels with evenly spaced indices, but
#     drop label == 64 if it slips in.

def build_xticks_labels(values):
    if not values:
        return [], []
    idxs = set([0, len(values) - 1])
    preferred = [32, 128, 256, 512, 1024, 2056, 3000]
    pos = {v: i for i, v in enumerate(values)}
    for v in preferred:
        if v in pos:
            idxs.add(pos[v])
    target = min(8, len(values))
    if len(idxs) < target:
        k = target
        for j in range(k):
            idx = int(round(j * (len(values) - 1) / max(1, (k - 1))))
            if values[idx] == 64:
                continue
            idxs.add(idx)
            if len(idxs) >= target:
                break
    idxs = sorted(idxs)
    ticks = [values[i] for i in idxs if values[i] != 64]
    labels = [str(v) for v in ticks]
    return ticks, labels

xticks, xlabels = build_xticks_labels(list(N))

fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(7.5, 7.5), sharex=True)

# Top subplot: Compression ratio vs Committee size (use a vivid green)
ax1.plot(N, ratio, marker='^', linestyle='--', color='#00aa00', label='Compression ratio (×)')
ax1.set_title('Compression Gain vs Committee Size')
ax1.set_ylabel('Compression ratio (×)')
ax1.grid(True, which='both', linestyle=':')
# Ensure the TOP subplot also shows x tick labels
ax1.set_xticks(xticks)
ax1.set_xticklabels(xlabels, rotation=45, ha='right', fontsize=9)
ax1.tick_params(axis='x', which='both', labelbottom=True)

# Bottom subplot: Persistent voters vs Committee size
ax2.plot(N, N, color='gray', linestyle='--', label='Committee size (y=x)')
ax2.plot(N, pv, marker='o', label='Persistent voters')
ax2.set_title('Persistent Voters vs Committee Size')
ax2.set_xlabel('Committee size (N)')
ax2.set_ylabel('Count')
ax2.grid(True, which='both', linestyle=':')
ax2.set_xticks(xticks)
ax2.set_xticklabels(xlabels, rotation=45, ha='right', fontsize=9)
ax2.legend(loc='best')

plt.tight_layout()
plt.subplots_adjust(bottom=0.14)
plt.savefig(png_path, dpi=160)
print(f"Wrote {png_path}")
PYFALLBACK

echo "Plot: ${PNG_PATH}"
if [[ $DO_OPEN -eq 1 ]] && command -v open >/dev/null 2>&1; then
  open "${PNG_PATH}" || true
fi
