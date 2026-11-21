#!/usr/bin/env python3
"""
Plot raw receive-side TCP samples from demo_bdp CSV output.

Usage:
  python3 plot.py <run.csv> [<run2.csv> ...] <out_dir>
"""

import math
import os
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


def ensure_log_span(ax, min_decades=3):
    """Ensure a log-scale axis shows at least min_decades of span, so the
    decade gridlines stay interpretable. If the autoscaled span is
    narrower, expand it geometrically around the data's center."""
    lo, hi = ax.get_ylim()
    if lo <= 0:
        return
    span = math.log10(hi / lo)
    if span >= min_decades:
        return
    center = math.sqrt(lo * hi)
    half = 10 ** (min_decades / 2)
    ax.set_ylim(center / half, center * half)


def parse_csv(path):
    header = {}
    rows = []
    with open(path) as f:
        for line in f:
            line = line.rstrip()
            if not line:
                continue
            if line.startswith("#"):
                for tok in line[1:].strip().split():
                    if "=" in tok:
                        k, v = tok.split("=", 1)
                        header[k] = v
                continue
            if line.startswith("t_s"):
                continue
            parts = line.split(",")
            if len(parts) != 5:
                continue
            rows.append((
                float(parts[0]),
                int(parts[1]),
                int(parts[2]),
                int(parts[3]),
                int(parts[4]),
            ))
    return header, rows


def plot_run(header, rows, out_path):
    ts  = [r[0] for r in rows]
    ns  = [r[1] for r in rows]
    cum = [r[2] for r in rows]
    rtt = [r[3] for r in rows]
    drate = [r[4] for r in rows]

    fig, axes = plt.subplots(5, 1, figsize=(10, 12), sharex=True)

    axes[0].plot(ts, [c / (1 << 20) for c in cum], ".-", markersize=2, color="C0")
    axes[0].set_ylabel("cum MB")
    axes[0].grid(True, alpha=0.3)

    # Raw per-read rate: ns[i] / (t[i] - t[i-1]).
    rates = []
    rate_ts = []
    for i in range(1, len(ts)):
        dt = ts[i] - ts[i - 1]
        if dt > 0:
            rates.append(ns[i] / dt / 1e6)
            rate_ts.append(ts[i])
    axes[1].plot(rate_ts, rates, ".", markersize=3, color="C1", alpha=0.3)
    axes[1].set_ylabel("per-read rate (MB/s)")
    axes[1].set_yscale("log")
    axes[1].grid(True, alpha=0.3, which="both")
    ensure_log_span(axes[1])

    # Clamped per-read rate: same data, but any dt below MIN_DT_S is
    # clamped up to MIN_DT_S before dividing. Below that floor you're
    # not sampling the network anymore — you're sampling the kernel's
    # own queue-drain dynamics. 1 ms comfortably exceeds the one-MSS-
    # at-line-rate time on any realistic link plus typical GRO
    # aggregation windows.
    MIN_DT_S = 0.001
    clamped_rates = []
    clamped_ts = []
    n_clamped = 0
    for i in range(1, len(ts)):
        dt = ts[i] - ts[i - 1]
        if dt > 0:
            if dt < MIN_DT_S:
                n_clamped += 1
                dt = MIN_DT_S
            clamped_rates.append(ns[i] / dt / 1e6)
            clamped_ts.append(ts[i])
    axes[2].plot(clamped_ts, clamped_rates, ".", markersize=3, color="C1", alpha=0.3)
    axes[2].set_ylabel("per-read rate (MB/s)\nclamped dt ≥ 1 ms")
    axes[2].set_yscale("log")
    axes[2].grid(True, alpha=0.3, which="both")
    axes[2].set_ylim(axes[1].get_ylim())
    pct = (100.0 * n_clamped / len(rate_ts)) if rate_ts else 0.0
    axes[2].set_title(f"{n_clamped} samples clamped ({pct:.1f}%)", fontsize=9)

    axes[3].plot(ts, [n / 1024 for n in ns], ".", markersize=3, color="C2", alpha=0.3)
    axes[3].set_ylabel("read() size (KB)")
    axes[3].set_yscale("log")
    axes[3].grid(True, alpha=0.3, which="both")
    ensure_log_span(axes[3])

    axes[4].plot(ts, [r / 1000.0 for r in rtt], ".-", markersize=2, color="C3")
    axes[4].set_ylabel("tcpi_rtt (ms)")
    axes[4].set_xlabel("time since request (s)")
    axes[4].grid(True, alpha=0.3)

    title = " | ".join(f"{k}={v}" for k, v in header.items())
    if any(d != 0 for d in drate):
        title += "  (tcpi_delivery_rate ≠ 0 somewhere — rare!)"
    else:
        title += "  (tcpi_delivery_rate ≡ 0 — the receiver-side blind spot)"
    fig.suptitle(title, fontsize=9)
    fig.tight_layout()
    fig.savefig(out_path, dpi=100)
    plt.close(fig)


def main():
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    csvs = sys.argv[1:-1]
    outdir = sys.argv[-1]
    os.makedirs(outdir, exist_ok=True)
    for csv_path in csvs:
        header, rows = parse_csv(csv_path)
        if not rows:
            print(f"  {csv_path}: no data, skipping", file=sys.stderr)
            continue
        base = os.path.splitext(os.path.basename(csv_path))[0]
        out = os.path.join(outdir, base + ".png")
        plot_run(header, rows, out)
        print(out)


if __name__ == "__main__":
    main()
