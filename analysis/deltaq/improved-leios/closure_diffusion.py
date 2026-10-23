#!/usr/bin/env python3
"""Reproduce tables and plots in docs/conditional-certification-diffusion.md.

Run from this directory with: python3 closure_diffusion.py
MB is decimal (1,000,000 bytes); analysis.py's kB is 1,000 bytes.
"""

from io import StringIO
from pathlib import Path

import numpy as np

import analysis as A
import two_phase as T
import matplotlib.pyplot as plt
from matplotlib.ticker import PercentFormatter


SIZES_MB = (0.125, 0.26, 0.5, 1, 2, 4, 8, 12, 12.288)
PLOT_DIR = Path(__file__).resolve().parents[3] / "docs" / "conditional-certification-diffusion"
# Pre-certification voters use blended paths; certified completion uses short paths.
DEFAULT_HOP_WEIGHTS = (0.5, 0.5)
DEFAULT_HOP_LABEL = "Before 7 s: blended fetching; recovery from 7 s: 50% one hop, 50% two hops"
BODY_CLOSURE_RATIO = 40 / 260


def save_plot(fig, name):
    PLOT_DIR.mkdir(parents=True, exist_ok=True)
    svg = StringIO()
    fig.savefig(svg, format="svg", bbox_inches="tight")
    (PLOT_DIR / name).write_text(
        "\n".join(line.rstrip() for line in svg.getvalue().splitlines()) + "\n"
    )
    plt.close(fig)


def plot_completion_cdfs(model, rows, active=False):
    fig, ax = plt.subplots(figsize=(10, 5.5), constrained_layout=True)
    colors = plt.get_cmap("tab10").colors
    for i, (mb, honest, adversarial) in enumerate(rows):
        cdf = adversarial if active else honest
        if cdf is None:
            continue  # Impossible certification has no conditional curve.
        ax.plot(
            A.TIMES, cdf, color=colors[i],
            linestyle="--" if mb == 12.288 else "-",
            label=f"{mb:g} MB" + (" (original case)" if mb == 12.288 else " (Musashi limit)" if mb == 0.26 else ""),
        )
    for t, label in ((7, "Vote deadline"), (10, "Checkpoint"), (14, "Diffusion deadline")):
        ax.axvline(t, color="gray", linestyle=":", linewidth=1)
        ax.text(t + 0.08, 0.03, f"{label}: {t} s", rotation=90, fontsize=8)
    population = "1,875 honest nodes; 25% active adversarial stake" if active else "2,500 honest nodes"
    ax.set_title(f"{model.upper()}: full closure completion given certification\n{population}; body = closure × 40/260\n{DEFAULT_HOP_LABEL}")
    ax.set_xlabel("Time from EB diffusion origin (s)")
    ax.set_ylabel("P(all honest nodes ready by t | certification)")
    ax.set_xlim(0, A.TIMES[-1])
    ax.set_ylim(0, 1.01)
    ax.yaxis.set_major_formatter(PercentFormatter(1))
    ax.grid(alpha=0.25)
    ax.legend(title="Closure size (decimal MB)", fontsize=8, loc="upper left")
    scenario = "active" if active else "honest"
    save_plot(fig, f"{model}-{scenario}-cdf.svg")


def plot_completion_times(results):
    fig, axes = plt.subplots(1, 2, figsize=(12, 5), sharey=True, constrained_layout=True)
    for ax, (model, rows) in zip(axes, results.items()):
        sizes = [row[0] for row in rows]
        for p, label in ((0.5, "Honest p50"), (0.95, "Honest p95"), (0.99, "Honest p99"), (0.999, "Honest p99.9")):
            ax.plot(sizes, [completion_quantile(row[1], p) for row in rows], marker="o", markersize=4, label=label)
        ax.plot(sizes, [completion_quantile(row[2], 0.99) for row in rows], linestyle="--", color="black", label="Active p99 (1,875 nodes)")
        ax.axhline(14, color="gray", linestyle=":", label="14 s deadline")
        ax.set_xscale("log", base=2)
        ticks = SIZES_MB[:-1]
        ax.set_xticks(ticks, [f"{s:g}" for s in ticks])
        ax.set_xlabel("Closure size (decimal MB; logarithmic scale)")
        ax.set_title(model.upper())
        ax.grid(alpha=0.25)
    axes[0].set_ylabel("All-node completion time given certification (s)")
    axes[1].legend(fontsize=8)
    fig.suptitle(f"Closure size and conditional completion-time percentiles; body = closure × 40/260\n{DEFAULT_HOP_LABEL}")
    save_plot(fig, "completion-time-percentiles.svg")


def check_cdf(cdf):
    assert np.all(np.isfinite(cdf))
    assert np.all((cdf >= 0) & (cdf <= 1))
    assert np.all(np.diff(cdf) >= -1e-12)


def percentage(p):
    return f"{100 * p:.4f}%"


def completion_quantile(cdf, p):
    return A.quantile_of(cdf, p) if cdf is not None else float("nan")


def seconds(t):
    return f"{t:.2f}" if np.isfinite(t) else "N/A"


def log_percentage(log_p):
    if not np.isfinite(log_p):
        return "0 (impossible)"
    if log_p >= np.log(0.0000005):
        return percentage(np.exp(log_p))
    log10_percent = log_p / np.log(10) + 2
    exponent = int(np.floor(log10_percent))
    return f"{10 ** (log10_percent - exponent):.4f}e{exponent:+d}%"


def main():
    print(A._committee_label())
    print(DEFAULT_HOP_LABEL)
    results = {}
    for model in ("mathis", "cubic"):
        rows = []
        A.set_network_model(model)
        print(f"\n## {model.upper()}\n")
        print("| Closure (MB) | Body (kB) | Missing txs (kB) | Voter ready by 7 s | P(C) | All ready by 7 s, given C | All ready by 10 s, given C | All ready by 14 s, given C |")
        print("|---:|---:|---:|---:|---:|---:|---:|---:|")
        timing_rows = []
        for mb in SIZES_MB:
            kb = mb * 1000
            body_kb = kb * BODY_CLOSURE_RATIO
            result = T.calculate(kb, body_kb, recovery_hops=DEFAULT_HOP_WEIGHTS)
            voter = result.voter
            check_cdf(voter)
            check_cdf(result.completion)
            gv = A.success_within(voter, 7)
            honest, active = result.honest, result.active
            for cdf in (honest, active):
                if cdf is not None:
                    check_cdf(cdf)
            rows.append((mb, honest, active))
            assert result.log_pc <= 0
            assert result.log_pc_active <= 0
            # Saturated certification reduces to the two-phase node-CDF power.
            if result.log_pc > np.log1p(-1e-12):
                assert np.allclose(honest, result.completion**2500, atol=1e-10, rtol=0)
            pc_text = log_percentage(result.log_pc)
            values = [percentage(gv), pc_text]
            values += [percentage(A.success_within(honest, t)) if honest is not None else "N/A" for t in (7, 10, 14)]
            print(f"| {mb:g} | {body_kb:g} | {kb / 6:g} | " + " | ".join(values) + " |")
            quantiles = [completion_quantile(honest, p) for p in (0.5, 0.95, 0.99, 0.999)]
            q_active = completion_quantile(active, 0.99)
            f_active = percentage(A.success_within(active, 14)) if active is not None else "N/A"
            timing_rows.append(
                f"| {mb:g} | " + " | ".join(seconds(q) for q in quantiles)
                + f" | {seconds(q_active)} | {f_active} |"
            )
        print("\n| Closure (MB) | Honest p50 (s) | Honest p95 (s) | Honest p99 (s) | Honest p99.9 (s) | Active p99 (s) | Active all ready by 14 s, given C |")
        print("|---:|---:|---:|---:|---:|---:|---:|")
        print("\n".join(timing_rows))
        results[model] = rows
        plot_completion_cdfs(model, rows)
        plot_completion_cdfs(model, rows, active=True)
    plot_completion_times(results)


if __name__ == "__main__":
    main()
