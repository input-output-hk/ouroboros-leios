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
import recovery_graph as G
import matplotlib.pyplot as plt
from matplotlib.ticker import PercentFormatter


SIZES_MB = (0.125, 0.26, 0.5, 1, 2, 4, 8, 12)
PLOT_DIR = (
    Path(__file__).resolve().parents[3] / "docs" / "conditional-certification-diffusion"
)
# Pre-certification voters use blended paths; certified completion uses the
# graph-derived law at the worst holder stake considered in the sweep.
DEFAULT_PATHS = G.derive_paths()
DEFAULT_HOP_WEIGHTS = DEFAULT_PATHS.recovery_weights()
DEFAULT_HOP_LABEL = (
    f"Before 7 s: blended fetching; recovery from 7 s: stake-weighted graph, "
    f"{DEFAULT_PATHS.peers} peers, {DEFAULT_PATHS.holder_stake:.0%} holder stake "
    f"({DEFAULT_HOP_WEIGHTS[0]:.1%} one hop, {sum(DEFAULT_HOP_WEIGHTS[1:]):.1%} two or more)"
)
BODY_CLOSURE_RATIO = 40 / 260


def save_plot(fig, name):
    PLOT_DIR.mkdir(parents=True, exist_ok=True)
    svg = StringIO()
    fig.savefig(svg, format="svg", bbox_inches="tight")
    (PLOT_DIR / name).write_text(
        "\n".join(line.rstrip() for line in svg.getvalue().splitlines()) + "\n"
    )
    plt.close(fig)


def plot_completion_cdfs(model, rows, active=False, stress=False):
    fig, ax = plt.subplots(figsize=(10, 5.5), constrained_layout=True)
    colors = plt.get_cmap("tab10").colors
    for i, (mb, honest, adversarial) in enumerate(rows):
        cdf = adversarial if active else honest
        if cdf is None:
            continue  # Impossible certification has no conditional curve.
        ax.plot(
            A.TIMES,
            cdf,
            color=colors[i],
            label=size_label(mb) + (" (Musashi limit)" if mb == 0.26 else ""),
        )
    for t, label in ((7, "Vote deadline"), (14, "Diffusion deadline")):
        ax.axvline(t, color="gray", linestyle=":", linewidth=1)
        ax.text(t + 0.08, 0.03, f"{label}: {t} s", rotation=90, fontsize=8)
    population = (
        "1,875 honest nodes; 25% active adversarial stake"
        if active
        else "2,500 honest nodes"
    )
    scenario_label = (
        "No prior availability: full-closure recovery"
        if stress
        else "Stationary-cache recovery"
    )
    ax.set_title(
        f"{model.upper()}: {scenario_label}\n{population}; body = closure × 40/260\n{DEFAULT_HOP_LABEL}"
    )
    ax.set_xlabel("Time from EB diffusion origin (s)")
    ax.set_ylabel("P(all honest nodes ready by t | certification)")
    ax.set_xlim(0, A.TIMES[-1])
    ax.set_ylim(0, 1.01)
    ax.yaxis.set_major_formatter(PercentFormatter(1))
    ax.grid(alpha=0.25)
    ax.legend(title="Closure size", fontsize=8, loc="lower right")
    scenario = "active" if active else "honest"
    save_plot(fig, f"{model}-{'stress-' if stress else ''}{scenario}-cdf.svg")


def plot_completion_times(results):
    fig, axes = plt.subplots(
        1, 2, figsize=(12, 5), sharey=True, constrained_layout=True
    )
    for ax, (model, rows) in zip(axes, results.items()):
        sizes = [row[0] for row in rows]
        for p, label in (
            (0.5, "Honest p50"),
            (0.95, "Honest p95"),
            (0.99, "Honest p99"),
            (0.999, "Honest p99.9"),
        ):
            ax.plot(
                sizes,
                [completion_quantile(row[1], p) for row in rows],
                marker="o",
                markersize=4,
                label=label,
            )
        ax.plot(
            sizes,
            [completion_quantile(row[2], 0.99) for row in rows],
            linestyle="--",
            color="black",
            label="Active p99 (1,875 nodes)",
        )
        ax.axhline(14, color="gray", linestyle=":", label="14 s deadline")
        ax.set_xscale("log", base=2)
        ticks = SIZES_MB
        ax.set_xticks(ticks, [size_label(s) for s in ticks])
        ax.set_xlabel("Closure size (logarithmic scale)")
        ax.set_title(model.upper())
        ax.grid(alpha=0.25)
    axes[0].set_ylabel("All-node completion time given certification (s)")
    axes[1].legend(fontsize=8)
    fig.suptitle(
        f"Closure size and conditional completion-time percentiles; body = closure × 40/260\n{DEFAULT_HOP_LABEL}"
    )
    save_plot(fig, "completion-time-percentiles.svg")


def check_cdf(cdf):
    assert np.all(np.isfinite(cdf))
    assert np.all((cdf >= 0) & (cdf <= 1))
    assert np.all(np.diff(cdf) >= -1e-12)


def percentage(p):
    # Two significant figures of p, or of 1 - p near one, to at most four
    # decimal places of a percentage.
    near_one = p >= 0.5
    x = 100 * (1 - p if near_one else p)
    if x < 0.0001:
        return ">99.9999%" if near_one else "<0.0001%"
    decimals = min(4, max(0, 1 - int(np.floor(np.log10(x)))))
    value = 100 - round(x, decimals) if near_one else round(x, decimals)
    return f"{value:.{decimals}f}%"


def size_label(mb):
    return f"{mb * 1000:g} kB" if mb < 1 else f"{mb:g} MB"


MODELS = (("mathis", "Mathis"), ("cubic", "CUBIC"))


def by_model(*names):
    return [f"{name}, {label}" for name in names for _, label in MODELS]


def print_table(title, header, rows):
    print(f"\n## {title}\n")
    print("| " + " | ".join(header) + " |")
    print("|" + "---:|" * len(header))
    for row in rows:
        print("| " + " | ".join(row) + " |")


def completion_quantile(cdf, p):
    return A.quantile_of(cdf, p) if cdf is not None else float("nan")


def seconds(t):
    if np.isposinf(t):
        return f">{A.TIMES[-1]:g}"
    return f"{t:.2f}" if np.isfinite(t) else "N/A"


def log_percentage(log_p):
    # Tails below 1e-20 depend on the finite permutation sample; bound them.
    if not np.isfinite(log_p):
        return "0 (impossible)"
    if log_p < np.log(1e-20):
        return "<10⁻¹⁸%"
    return percentage(np.exp(log_p))


def stress_scenario(baseline):
    fig, axes = plt.subplots(
        1, 2, figsize=(12, 5), sharey=True, constrained_layout=True
    )
    cells, active_gain = {}, {}
    for ax, (model, base_rows) in zip(axes, baseline.items()):
        A.set_network_model(model)
        rows = []
        for mb, base_honest, _ in base_rows:
            result = T.calculate(
                mb * 1000,
                mb * 1000 * BODY_CLOSURE_RATIO,
                recovery_hops=DEFAULT_HOP_WEIGHTS,
                stress=True,
            )
            for cdf in (result.voter, result.completion, result.honest, result.active):
                if cdf is not None:
                    check_cdf(cdf)
            rows.append((mb, result.honest, result.active))
            times = [
                completion_quantile(base_honest, 0.99),
                completion_quantile(result.honest, 0.99),
                completion_quantile(result.honest, 0.999),
            ]
            ready = (
                percentage(A.success_within(result.honest, 14))
                if result.honest is not None
                else "N/A"
            )
            cells[model, mb] = [seconds(t) for t in times] + [ready]
            # Active stress p99 against honest stress p99, where both are finite.
            gain = times[1] - completion_quantile(result.active, 0.99)
            if np.isfinite(gain):
                active_gain.setdefault(model, []).append(gain)
        plot_completion_cdfs(model, rows, stress=True)
        for scenario_rows, name, color in (
            (base_rows, "Stationary cache", "tab:blue"),
            (rows, "No prior availability", "tab:red"),
        ):
            for p, style in ((0.99, "-"), (0.999, "--")):
                values = [completion_quantile(row[1], p) for row in scenario_rows]
                censored = [s for s, v in zip(SIZES_MB, values) if np.isposinf(v)]
                values = [v if np.isfinite(v) else np.nan for v in values]
                ax.plot(
                    SIZES_MB,
                    values,
                    color=color,
                    linestyle=style,
                    marker="o",
                    markersize=4,
                    label=f"{name}, p{100*p:g}",
                )
                if censored and p == 0.99:
                    ax.scatter(
                        censored,
                        [A.TIMES[-1]] * len(censored),
                        color=color,
                        marker="^",
                        label=f"{name}: >{A.TIMES[-1]:g} s",
                    )
        ax.set_xscale("log", base=2)
        ax.set_xticks(SIZES_MB, [size_label(mb) for mb in SIZES_MB])
        ax.set(title=model.upper(), xlabel="Closure size (logarithmic scale)")
        ax.axhline(14, color="gray", linestyle=":", label="14 s deadline")
        ax.grid(alpha=0.25)
        ax.legend(fontsize=7)
    axes[0].set_ylabel("All-node completion time given certification (s)")
    fig.suptitle(
        "Full-closure recovery stress versus stationary-cache baseline\nSame phase-one certification and graph-derived recovery hops from 7 s"
    )
    save_plot(fig, "stress-completion-time-percentiles.svg")
    print_table(
        "No-prior-availability stress",
        ["Closure"]
        + by_model(
            "Baseline p99", "Stress p99", "Stress p99.9", "Stress ready by 14 s"
        ),
        [
            [size_label(mb)]
            + [cells[model, mb][i] for i in range(4) for model, _ in MODELS]
            for mb in SIZES_MB
        ],
    )
    for model, label in MODELS:
        gains = active_gain[model]
        assert min(gains) > -0.005  # The active target is never later.
        print(
            f"\n{label} active stress p99 is {abs(min(gains)):.2f} to "
            f"{max(gains):.2f} s earlier than stress p99"
        )


# (adversarial stake, honest holder stake = tau - adversarial stake), both of total stake.
SAFETY_SCENARIOS = ((0.25, 0.5), (0.5, 0.25))


def safety_worst_case(baseline):
    fig, axes = plt.subplots(
        1, 2, figsize=(12, 5), sharey=True, constrained_layout=True
    )
    for ax, (model, base_rows) in zip(axes, baseline.items()):
        A.set_network_model(model)
        curves, table, receiver_counts = {}, [], {}
        for mb in SIZES_MB:
            row = [size_label(mb)]
            for adversary, holder in SAFETY_SCENARIOS:
                paths = G.derive_paths(holder, G.DEFAULT_PEERS, adversary)
                receivers = round(paths.receivers / paths.trials)
                _, everyone = T.worst_case(
                    mb * 1000,
                    mb * 1000 * BODY_CLOSURE_RATIO,
                    receivers,
                    paths.recovery_weights(),
                )
                check_cdf(everyone)
                times = [completion_quantile(everyone, q) for q in (0.5, 0.99)]
                curves.setdefault(adversary, []).append(times[1])
                receiver_counts[adversary] = receivers
                row += [seconds(t) for t in times]
                row += [percentage(A.success_within(everyone, t)) for t in (14, 20)]
            table.append(row)
        label = dict(MODELS)[model]
        print_table(
            f"{label} late-release safety worst case",
            ["Closure"]
            + [
                f"{name}, {adversary:.0%}"
                for adversary, _ in SAFETY_SCENARIOS
                for name in ("p50", "p99", "Ready by 14 s", "Ready by 20 s")
            ],
            table,
        )
        print(
            "\nReceivers: "
            + ", ".join(
                f"{n:,} at {a:.0%} adversarial stake"
                for a, n in receiver_counts.items()
            )
        )
        ax.plot(
            SIZES_MB,
            [completion_quantile(row[1], 0.99) for row in base_rows],
            color="tab:blue",
            marker="o",
            markersize=4,
            label="Honest baseline, p99",
        )
        # Censored markers share a position, so nudge each scenario sideways
        # (multiplicatively, on the logarithmic axis) to keep both visible.
        for (adversary, holder), color, nudge in zip(
            SAFETY_SCENARIOS, ("tab:orange", "tab:red"), (0.94, 1.06)
        ):
            values = curves[adversary]
            censored = [mb for mb, v in zip(SIZES_MB, values) if np.isposinf(v)]
            ax.plot(
                SIZES_MB,
                [v if np.isfinite(v) else np.nan for v in values],
                color=color,
                marker="o",
                markersize=4,
                label=f"{adversary:.0%} adversarial stake, {holder:.0%} honest holders, p99",
            )
            if censored:
                ax.scatter(
                    [mb * nudge for mb in censored],
                    [A.TIMES[-1]] * len(censored),
                    color=color,
                    marker="^",
                    label=f"{adversary:.0%} adversarial: >{A.TIMES[-1]:g} s",
                )
        ax.axhline(14, color="gray", linestyle=":", label="14 s deadline")
        ax.set_xscale("log", base=2)
        ax.set_xticks(SIZES_MB, [size_label(mb) for mb in SIZES_MB])
        ax.set(title=model.upper(), xlabel="Closure size (logarithmic scale)")
        ax.grid(alpha=0.25)
        ax.legend(fontsize=7)
    axes[0].set_ylabel("All-honest-node completion time (s)")
    fig.suptitle(
        "Late-release worst case: only τ − σ_α honest stake holds the EB at 7 s\n"
        "Receivers fetch body and full closure over the adversary-aware graph, then validate"
    )
    save_plot(fig, "safety-worst-case-percentiles.svg")


def graph_path_report():
    # Sampled frequencies: two decimals, since sampling error exceeds finer precision.
    print("\n## Graph-derived recovery paths\n")
    print(
        "| Peers | Holder stake | Adversarial stake | One hop | Closed form | Two hops | Three+ hops | Unreachable | All reachable |"
    )
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    sweep = G.sweep()
    for paths in sweep:
        weights = paths.weights
        values = [
            weights[0],
            G.one_hop_closed_form(paths.holder_stake, paths.peers),
            weights[1] if len(weights) > 1 else 0.0,
            sum(weights[2:]),
            paths.unreachable,
            paths.all_reachable,
        ]
        print(
            f"| {paths.peers} | {paths.holder_stake:.0%} | {paths.adversary_stake:.0%} | "
            + " | ".join(f"{100 * v:.2f}%" for v in values)
            + " |"
        )
    fig, ax = plt.subplots(figsize=(8, 5), constrained_layout=True)
    grid = np.linspace(0.05, 0.95, 91)
    colors = plt.get_cmap("tab10").colors
    for color, peers in zip(colors, G.PEER_COUNTS):
        honest = [p for p in sweep if p.peers == peers and p.adversary_stake == 0]
        ax.plot(
            grid,
            G.one_hop_closed_form(grid, peers),
            color=color,
            linestyle="--",
            linewidth=1,
        )
        ax.plot(
            [p.holder_stake for p in honest],
            [p.weights[0] for p in honest],
            "o",
            color=color,
            label=f"{peers} peers: graph sample; dashed: 1 − (1 − f)^{peers}",
        )
    ax.set(
        xlabel="Holder stake f",
        ylabel="P(nearest holder is one hop away)",
        ylim=(0, 1.02),
    )
    ax.xaxis.set_major_formatter(PercentFormatter(1))
    ax.yaxis.set_major_formatter(PercentFormatter(1))
    ax.grid(alpha=0.25)
    ax.legend(fontsize=8, loc="lower right")
    ax.set_title(
        f"One-hop recovery probability, {G.N_NODES:,} nodes, stake-weighted distinct peers\n"
        f"No adversaries; remaining reachable receivers are two or more hops away"
    )
    save_plot(fig, "graph-recovery-paths.svg")


def main():
    print(A._committee_label())
    print(DEFAULT_HOP_LABEL)
    results, cells = {}, {}
    for model, _ in MODELS:
        rows = []
        A.set_network_model(model)
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
            ready = [
                percentage(A.success_within(honest, t)) if honest is not None else "N/A"
                for t in (7, 14)
            ]
            quantiles = [
                seconds(completion_quantile(honest, p))
                for p in (0.5, 0.95, 0.99, 0.999)
            ]
            f_active = (
                percentage(A.success_within(active, 14))
                if active is not None
                else "N/A"
            )
            cells[model, mb] = dict(
                voter=percentage(gv),
                pc=log_percentage(result.log_pc),
                ready7=ready[0],
                ready14=ready[1],
                p50=quantiles[0],
                p95=quantiles[1],
                p99=quantiles[2],
                p999=quantiles[3],
                active_p99=seconds(completion_quantile(active, 0.99)),
                active14=f_active,
            )
        results[model] = rows
        plot_completion_cdfs(model, rows)
        plot_completion_cdfs(model, rows, active=True)

    def table(title, names, keys, lead=lambda mb: []):
        print_table(
            title,
            ["Closure"] + names + by_model(*keys.values()),
            [
                [size_label(mb)]
                + lead(mb)
                + [cells[model, mb][key] for key in keys for model, _ in MODELS]
                for mb in SIZES_MB
            ],
        )

    table(
        "Certification",
        ["Body (kB)", "Missing txs (kB)"],
        {"voter": "Voter ready by 7 s", "pc": "$P(C)$"},
        lambda mb: [
            f"{mb * 1000 * BODY_CLOSURE_RATIO:,.0f}",
            f"{mb * 1000 / 6:,.0f}",
        ],
    )
    table(
        "All honest nodes ready, given certification",
        [],
        {"ready7": "By 7 s", "ready14": "By 14 s"},
    )
    table(
        "Completion times (s)",
        [],
        {"p50": "p50", "p95": "p95", "p99": "p99", "p999": "p99.9"},
    )
    table(
        "Active adversarial voting",
        [],
        {
            "p99": "Honest p99",
            "active_p99": "Active p99",
            "active14": "Active ready by 14 s",
        },
    )
    plot_completion_times(results)
    stress_scenario(results)
    safety_worst_case(results)
    graph_path_report()


if __name__ == "__main__":
    main()
