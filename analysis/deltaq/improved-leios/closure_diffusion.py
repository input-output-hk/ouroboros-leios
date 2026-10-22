#!/usr/bin/env python3
"""Reproduce tables and plots in docs/conditional-certification-diffusion.md.

Run from this directory with: python3 closure_diffusion.py
MB is decimal (1,000,000 bytes); analysis.py's kB is 1,000 bytes.
"""

from io import StringIO
from pathlib import Path

import numpy as np

import analysis as A
import matplotlib.pyplot as plt
from matplotlib.ticker import PercentFormatter


SIZES_MB = (0.125, 0.26, 0.5, 1, 2, 4, 8, 12, 12.288)
PLOT_DIR = Path(__file__).resolve().parents[3] / "docs" / "conditional-certification-diffusion"


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
        ax.plot(
            A.TIMES, cdf, color=colors[i],
            linestyle="--" if mb == 12.288 else "-",
            label=f"{mb:g} MB" + (" (original case)" if mb == 12.288 else " (Musashi limit)" if mb == 0.26 else ""),
        )
    for t, label in ((7, "Vote deadline"), (10, "Checkpoint"), (14, "Diffusion deadline")):
        ax.axvline(t, color="gray", linestyle=":", linewidth=1)
        ax.text(t + 0.08, 0.03, f"{label}: {t} s", rotation=90, fontsize=8)
    population = "1,875 honest nodes; 25% active adversarial stake" if active else "2,500 honest nodes"
    ax.set_title(f"{model.upper()}: full closure completion given certification\n{population}")
    ax.set_xlabel("Time from EB diffusion origin (s)")
    ax.set_ylabel("P(all honest nodes ready by t | certification)")
    ax.set_xlim(4, 15)
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
            ax.plot(sizes, [A.quantile_of(row[1], p) for row in rows], marker="o", markersize=4, label=label)
        ax.plot(sizes, [A.quantile_of(row[2], 0.99) for row in rows], linestyle="--", color="black", label="Active p99 (1,875 nodes)")
        ax.axhline(14, color="gray", linestyle=":", label="14 s deadline")
        ax.set_xscale("log", base=2)
        ticks = SIZES_MB[:-1]
        ax.set_xticks(ticks, [f"{s:g}" for s in ticks])
        ax.set_xlabel("Closure size (decimal MB; logarithmic scale)")
        ax.set_title(model.upper())
        ax.grid(alpha=0.25)
    axes[0].set_ylabel("All-node completion time given certification (s)")
    axes[1].legend(fontsize=8)
    fig.suptitle("Closure size and conditional completion-time percentiles")
    save_plot(fig, "completion-time-percentiles.svg")


def check_cdf(cdf):
    assert np.all(np.isfinite(cdf))
    assert np.all((cdf >= 0) & (cdf <= 1))
    assert np.all(np.diff(cdf) >= -1e-12)


def percentage(p):
    return f"{100 * p:.4f}%"


def main():
    print(A._committee_label())
    results = {}
    for model in ("mathis", "cubic"):
        rows = []
        A.set_network_model(model)
        print(f"\n## {model.upper()}\n")
        print("| Closure (MB) | Missing txs (kB) | Voter ready by 7 s | P(C) | All ready by 7 s, given C | All ready by 10 s, given C | All ready by 14 s, given C |")
        print("|---:|---:|---:|---:|---:|---:|---:|")
        timing_rows = []
        for mb in SIZES_MB:
            kb = mb * 1000
            voter = A.cdf_closure_completion(kb)
            apply = A.cdf_closure_completion(kb, reapply_only=True)
            check_cdf(voter)
            check_cdf(apply)
            gv = A.success_within(voter, 7)
            pc = float(A._quorum_given_honest_ontime(gv, 2500, 0.75, 0, "active"))
            honest = A.cdf_full_closure_diffusion_given_cert(kb)
            active = A.cdf_full_closure_diffusion_given_cert(kb, beta=0.25)
            for cdf in (honest, active):
                check_cdf(cdf)
            rows.append((mb, honest, active))
            # In these rows certification saturates: the implementation's
            # conditional result should match its reapply-only power term.
            assert pc > 1 - 1e-12
            assert np.allclose(honest, apply**2500, atol=1e-10, rtol=0)
            values = [percentage(gv), percentage(pc)]
            values += [percentage(A.success_within(honest, t)) for t in (7, 10, 14)]
            print(f"| {mb:g} | {kb / 6:g} | " + " | ".join(values) + " |")
            quantiles = [A.quantile_of(honest, p) for p in (0.5, 0.95, 0.99, 0.999)]
            q_active = A.quantile_of(active, 0.99)
            f_active = A.success_within(active, 14)
            timing_rows.append(
                f"| {mb:g} | " + " | ".join(f"{q:.2f}" for q in quantiles)
                + f" | {q_active:.2f} | {percentage(f_active)} |"
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
