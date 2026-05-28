#!/usr/bin/env python3
"""Overlay whole-file download-time CDFs for several n-chunk parallel scenarios.

For each n, simulates the chunk-size distribution (file_size_kb / n) and renders
the implied whole-file CDF F_file(t) = F_chunk(t)^n on a single SVG axes. As n
grows the curves shift left and the right tail collapses — the visual signature
of chunking's benefit.

Usage:
  tools/plot_chunking.py [config.yaml] [-o output.svg] [--ns 1,2,4,8,16,32]
                         [--runs 50000] [--scenario optimistic|realistic]
                         [--xmax SECONDS] [--cdfmin Y_MIN]
                         [--ci [--ci-runs 500] [--ci-alpha 0.05]]
"""
from __future__ import annotations

import argparse
import dataclasses
import math
import random
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))
import estimator  # noqa: E402


PALETTE = [
    "#d62728",  # red    — n=1 (baseline, slowest tail)
    "#ff7f0e",  # orange
    "#bcbd22",  # olive
    "#2ca02c",  # green
    "#17becf",  # cyan
    "#1f77b4",  # blue   — n=large (fastest tail)
    "#9467bd",  # purple — overflow
    "#8c564b",  # brown
]


def _bdp_ssthresh(link_mbps: float, rtt_s: float, mss: int) -> float:
    return max(1.0, math.floor(link_mbps * 1e6 * rtt_s / 8.0 / mss))


def simulate_chunk(base: estimator.Config, n: int, scenario: str) -> list[float]:
    chunk_kb = base.file_size_kb / n
    link = (
        base.link_speed_mbps if scenario == "optimistic" else base.link_speed_mbps / n
    )
    cfg = dataclasses.replace(
        base,
        file_size_kb=chunk_kb,
        link_speed_mbps=link,
        initial_ssthresh_segs=_bdp_ssthresh(link, base.rtt_s, base.mss_bytes),
    )
    return sorted(estimator.monte_carlo(cfg))


def compute_x_max(
    curves: list[tuple[int, list[float]]], override: float | None
) -> float:
    """Auto x-axis cap: 0.5 s past the slowest curve's whole-file P99."""
    if override is not None:
        return float(override)
    all_finite = [t for _, ts in curves for t in ts if math.isfinite(t)]
    if not all_finite:
        return 1.0
    p99_times: list[float] = []
    for n, ts in curves:
        finite_ts = [t for t in ts if math.isfinite(t)]
        if not finite_ts:
            continue
        q = 0.99 ** (1.0 / n)
        p99_times.append(estimator.percentile_of(finite_ts, q))
    return max(p99_times) + 0.5 if p99_times else max(all_finite) * 1.05


def fmt_y(step: float, v: float):
    if step >= 0.1 - 1e-9:
        return f"{v:.1f}"
    if step >= 0.01 - 1e-9:
        return f"{v:.2f}"
    if step >= 0.001 - 1e-9:
        return f"{v:.3f}"
    return f"{v:.4f}"


def render(
    curves: list[tuple[int, list[float]]],
    base: estimator.Config,
    scenario: str,
    out_path: Path,
    x_max_override: float | None = None,
    y_min: float = 0.0,
) -> None:
    """Render overlaid file CDFs (F_chunk^n) for the given (n, sorted_times) pairs."""
    width = 960
    height = 600
    margin_left = 80
    margin_right = 30
    margin_top = 70
    margin_bottom = 60
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom

    # x range: caller supplies the cap (computed once via compute_x_max so the
    # per-n CI plots can share it with the multi-curve plot).
    x_min = 0.0
    x_max = compute_x_max(curves, x_max_override)

    # y_min < 1 lets the user zoom into the top of the CDF where curves cross
    # P99. y-axis now spans [y_min, 1.0] mapped to the full plot height.
    y_min = max(0.0, min(0.9999, float(y_min)))
    y_span = 1.0 - y_min

    def x_to_px(x: float) -> float:
        return margin_left + (x - x_min) / (x_max - x_min) * plot_w

    def y_to_px(y: float) -> float:
        return margin_top + (1.0 - (y - y_min) / y_span) * plot_h

    parts: list[str] = []
    parts.append(
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" '
        f'font-family="Helvetica, Arial, sans-serif" font-size="12">'
    )
    parts.append('<rect width="100%" height="100%" fill="white"/>')

    parts.append(
        f'<text x="{width/2:.1f}" y="22" text-anchor="middle" font-size="16" '
        f'font-weight="bold">Chunking benefit: whole-file download CDF vs n parallel chunks</text>'
    )
    sub1 = (
        f"size={base.file_size_kb:g} kB, link={base.link_speed_mbps:g} Mbps, "
        f"RTT={base.rtt_ms:g} ms, p={base.effective_loss_rate():.2e}"
    )
    sub2 = (
        f"scenario={scenario} (each chunk gets "
        f"{'full link' if scenario == 'optimistic' else 'link/n'}), "
        f"runs={base.monte_carlo_runs}; curves are F_chunk(t)^n"
    )
    parts.append(
        f'<text x="{width/2:.1f}" y="40" text-anchor="middle" fill="#555">{sub1}</text>'
    )
    parts.append(
        f'<text x="{width/2:.1f}" y="56" text-anchor="middle" fill="#555">{sub2}</text>'
    )

    parts.append(
        f'<rect x="{margin_left}" y="{margin_top}" '
        f'width="{plot_w}" height="{plot_h}" fill="#fafafa" stroke="#888"/>'
    )

    # Gridlines + tick labels.
    n_x = 8
    n_y = 10
    x_ticks = [x_min + (x_max - x_min) * i / n_x for i in range(n_x + 1)]
    y_step = y_span / n_y
    y_ticks = [y_min + y_step * i for i in range(n_y + 1)]

    def fmt_x(v: float) -> str:
        if v >= 100:
            return f"{v:.0f}"
        if v >= 10:
            return f"{v:.1f}"
        if v >= 1:
            return f"{v:.2f}"
        return f"{v:.3f}"

    for tv in x_ticks:
        px = x_to_px(tv)
        parts.append(
            f'<line x1="{px:.2f}" y1="{margin_top}" x2="{px:.2f}" '
            f'y2="{margin_top + plot_h}" stroke="#e0e0e0"/>'
        )
        parts.append(
            f'<text x="{px:.2f}" y="{margin_top + plot_h + 16}" '
            f'text-anchor="middle" fill="#333">{fmt_x(tv)}</text>'
        )
    for tv in y_ticks:
        py = y_to_px(tv)
        parts.append(
            f'<line x1="{margin_left}" y1="{py:.2f}" '
            f'x2="{margin_left + plot_w}" y2="{py:.2f}" stroke="#e0e0e0"/>'
        )
        parts.append(
            f'<text x="{margin_left - 8}" y="{py + 4:.2f}" '
            f'text-anchor="end" fill="#333">{fmt_y(y_step, tv)}</text>'
        )

    # P99 reference line — only when 0.99 is inside the visible y range.
    if 0.99 >= y_min:
        py99 = y_to_px(0.99)
        parts.append(
            f'<line x1="{margin_left}" y1="{py99:.2f}" '
            f'x2="{margin_left + plot_w}" y2="{py99:.2f}" stroke="#888" '
            f'stroke-width="1" stroke-dasharray="4,4"/>'
        )
        parts.append(
            f'<text x="{margin_left + plot_w - 6:.2f}" y="{py99 - 4:.2f}" '
            f'text-anchor="end" fill="#555" font-style="italic">P99</text>'
        )

    parts.append(
        f'<text x="{margin_left + plot_w/2:.1f}" y="{height - 15}" '
        f'text-anchor="middle">Download time (seconds)</text>'
    )
    parts.append(
        f'<text transform="translate(20,{margin_top + plot_h/2:.1f}) rotate(-90)" '
        f'text-anchor="middle">Cumulative probability  (whole-file)</text>'
    )

    # One polyline per (n, sorted_chunk_times), F_file(t) = F_chunk(t)^n.
    # Downsample to ~1000 sample points per curve so the SVG stays compact;
    # at this density a connected polyline is visually indistinguishable from
    # the per-sample step plot. When y_min > 0 we downsample within the visible
    # y-range only so the zoomed view doesn't lose tail detail. Curves enter
    # the plot from the bottom at their y_min crossing point; if x_max
    # truncates them, the polyline ends cleanly at the right edge.
    max_pts = 1000
    for idx, (n, sorted_times) in enumerate(curves):
        color = PALETTE[idx % len(PALETTE)]
        finite = [t for t in sorted_times if math.isfinite(t)]
        N = len(finite)
        if N == 0:
            continue

        # First sample index where ((i+1)/N)^n >= y_min:
        #   (i+1)/N >= y_min^(1/n)   ⇒   i >= N · y_min^(1/n) − 1
        if y_min > 0.0:
            i_min = max(0, int(math.ceil(N * (y_min ** (1.0 / n)) - 1.0)))
        else:
            i_min = 0
        if i_min >= N:
            continue  # curve never reaches y_min within sampled data

        n_visible = N - i_min
        step = max(1, n_visible // max_pts)
        indices = list(range(i_min, N, step))
        if indices[-1] != N - 1:
            indices.append(N - 1)

        pts: list[tuple[float, float]] = []
        last_y_in_range = y_min
        truncated = False
        for i in indices:
            x_data = finite[i]
            if x_data > x_max:
                truncated = True
                break
            y = ((i + 1) / N) ** n
            if y < y_min:
                continue
            if not pts:
                # Anchor curve's entry into the visible plot. When y_min == 0
                # we start at the bottom-left corner so the CDF has a 0
                # baseline; otherwise we anchor at the y_min crossing x.
                anchor_x = x_min if y_min == 0.0 else x_data
                pts.append((x_to_px(anchor_x), y_to_px(y_min)))
            pts.append((x_to_px(x_data), y_to_px(y)))
            last_y_in_range = y

        if pts:
            pts.append((x_to_px(x_max), y_to_px(last_y_in_range if truncated else 1.0)))
            polyline = " ".join(f"{x:.2f},{y:.2f}" for x, y in pts)
            parts.append(
                f'<polyline points="{polyline}" fill="none" stroke="{color}" '
                f'stroke-width="1.8"/>'
            )

    # Legend in the lower-right of the plot. Header wrapped to two lines at a
    # slightly smaller font so it fits the box without being truncated.
    legend_w = 110
    header_h = 30  # two header lines (14 px line height) + a few px slack
    entry_h = 18
    legend_h = header_h + entry_h * len(curves) + 8
    legend_x = margin_left + plot_w - legend_w - 12
    legend_y = margin_top + plot_h - legend_h - 12
    parts.append(
        f'<rect x="{legend_x}" y="{legend_y}" width="{legend_w}" height="{legend_h}" '
        f'fill="white" fill-opacity="0.85" stroke="#888"/>'
    )
    parts.append(
        f'<text x="{legend_x + 8}" y="{legend_y + 14}" font-size="11" '
        f'font-weight="bold">n parallel</text>'
    )
    parts.append(
        f'<text x="{legend_x + 8}" y="{legend_y + 28}" font-size="11" '
        f'font-weight="bold">chunks</text>'
    )
    for idx, (n, _) in enumerate(curves):
        color = PALETTE[idx % len(PALETTE)]
        ly = legend_y + header_h + (idx + 1) * entry_h - 4
        parts.append(
            f'<line x1="{legend_x + 8}" y1="{ly - 4}" '
            f'x2="{legend_x + 36}" y2="{ly - 4}" stroke="{color}" stroke-width="2.2"/>'
        )
        parts.append(f'<text x="{legend_x + 44}" y="{ly}">n = {n}</text>')

    parts.append("</svg>")
    out_path.write_text("\n".join(parts))


def render_ci(
    n: int,
    sorted_times: list[float],
    color: str,
    base: estimator.Config,
    scenario: str,
    out_path: Path,
    x_max: float,
    y_min: float = 0.0,
    B: int = 500,
    alpha: float = 0.05,
) -> None:
    """Render a single n's whole-file CDF with a pointwise bootstrap CI band.

    The CI band is computed via the exact bootstrap distribution of an
    empirical CDF at a fixed t: F_chunk_b(t) ~ Binomial(N, F_orig(t))/N. Each
    bootstrap draw is then mapped to F_file_b = F_chunk_b^n, and the band is
    the [alpha/2, 1-alpha/2] quantile envelope of those B draws at each t.

    NOTE: the band is *pointwise* and shows uncertainty at fixed t. It can
    under-report the uncertainty in the *quantile* (read off horizontally
    at y=0.99) wherever the CDF has a step. Use tools/chunking_stability.py
    for a seed-to-seed sanity check on the quantile.
    """
    width = 960
    height = 600
    margin_left = 80
    margin_right = 30
    margin_top = 70
    margin_bottom = 60
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom

    x_min = 0.0
    y_min = max(0.0, min(0.9999, float(y_min)))
    y_span = 1.0 - y_min

    def x_to_px(x: float) -> float:
        return margin_left + (x - x_min) / (x_max - x_min) * plot_w

    def y_to_px(y: float) -> float:
        return margin_top + (1.0 - (y - y_min) / y_span) * plot_h

    parts: list[str] = []
    parts.append(
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" '
        f'font-family="Helvetica, Arial, sans-serif" font-size="12">'
    )
    parts.append('<rect width="100%" height="100%" fill="white"/>')

    parts.append(
        f'<text x="{width/2:.1f}" y="22" text-anchor="middle" font-size="16" '
        f'font-weight="bold">Chunking benefit: n = {n} parallel chunks '
        f"(pointwise {(1-alpha)*100:g}% bootstrap CI)</text>"
    )
    sub1 = (
        f"size={base.file_size_kb:g} kB, link={base.link_speed_mbps:g} Mbps, "
        f"RTT={base.rtt_ms:g} ms, p={base.effective_loss_rate():.2e}"
    )
    sub2 = (
        f"scenario={scenario}, runs={base.monte_carlo_runs}, "
        f"bootstrap B={B}; curve is F_chunk(t)^n"
    )
    parts.append(
        f'<text x="{width/2:.1f}" y="40" text-anchor="middle" fill="#555">{sub1}</text>'
    )
    parts.append(
        f'<text x="{width/2:.1f}" y="56" text-anchor="middle" fill="#555">{sub2}</text>'
    )

    parts.append(
        f'<rect x="{margin_left}" y="{margin_top}" '
        f'width="{plot_w}" height="{plot_h}" fill="#fafafa" stroke="#888"/>'
    )

    # Gridlines + tick labels (same scheme as the multi-curve plot).
    n_x_t, n_y_t = 8, 10
    x_ticks = [x_min + (x_max - x_min) * i / n_x_t for i in range(n_x_t + 1)]
    y_step = y_span / n_y_t
    y_ticks = [y_min + y_step * i for i in range(n_y_t + 1)]

    def fmt_x(v: float) -> str:
        if v >= 100:
            return f"{v:.0f}"
        if v >= 10:
            return f"{v:.1f}"
        if v >= 1:
            return f"{v:.2f}"
        return f"{v:.3f}"

    for tv in x_ticks:
        px = x_to_px(tv)
        parts.append(
            f'<line x1="{px:.2f}" y1="{margin_top}" x2="{px:.2f}" '
            f'y2="{margin_top + plot_h}" stroke="#e0e0e0"/>'
        )
        parts.append(
            f'<text x="{px:.2f}" y="{margin_top + plot_h + 16}" '
            f'text-anchor="middle" fill="#333">{fmt_x(tv)}</text>'
        )
    for tv in y_ticks:
        py = y_to_px(tv)
        parts.append(
            f'<line x1="{margin_left}" y1="{py:.2f}" '
            f'x2="{margin_left + plot_w}" y2="{py:.2f}" stroke="#e0e0e0"/>'
        )
        parts.append(
            f'<text x="{margin_left - 8}" y="{py + 4:.2f}" '
            f'text-anchor="end" fill="#333">{fmt_y(y_step, tv)}</text>'
        )

    if 0.99 >= y_min:
        py99 = y_to_px(0.99)
        parts.append(
            f'<line x1="{margin_left}" y1="{py99:.2f}" '
            f'x2="{margin_left + plot_w}" y2="{py99:.2f}" stroke="#888" '
            f'stroke-width="1" stroke-dasharray="4,4"/>'
        )
        parts.append(
            f'<text x="{margin_left + plot_w - 6:.2f}" y="{py99 - 4:.2f}" '
            f'text-anchor="end" fill="#555" font-style="italic">P99</text>'
        )

    parts.append(
        f'<text x="{margin_left + plot_w/2:.1f}" y="{height - 15}" '
        f'text-anchor="middle">Download time (seconds)</text>'
    )
    parts.append(
        f'<text transform="translate(20,{margin_top + plot_h/2:.1f}) rotate(-90)" '
        f'text-anchor="middle">Cumulative probability  (whole-file)</text>'
    )

    # Visible-range sampling (same as render()).
    finite = [t for t in sorted_times if math.isfinite(t)]
    N = len(finite)
    if N == 0:
        parts.append("</svg>")
        out_path.write_text("\n".join(parts))
        return
    if y_min > 0.0:
        i_min = max(0, int(math.ceil(N * (y_min ** (1.0 / n)) - 1.0)))
    else:
        i_min = 0
    if i_min >= N:
        parts.append("</svg>")
        out_path.write_text("\n".join(parts))
        return

    max_pts = 1000
    n_visible = N - i_min
    step = max(1, n_visible // max_pts)
    indices = list(range(i_min, N, step))
    if indices[-1] != N - 1:
        indices.append(N - 1)

    # Bootstrap-sample F_chunk(x_i) ~ Binomial(N, (i+1)/N) / N for each x_i,
    # then transform to F_file = F_chunk^n. The B-sample envelope at quantile
    # alpha/2 and 1-alpha/2 is our pointwise CI band.
    rng = random.Random(0)
    lo_q_idx = int(alpha / 2.0 * B)
    hi_q_idx = min(B - 1, int((1.0 - alpha / 2.0) * B))

    band: list[tuple[float, float, float, float]] = []  # (x, lo_y, hi_y, point_y)
    truncated = False
    for i in indices:
        x_data = finite[i]
        if x_data > x_max:
            truncated = True
            break
        F_orig = (i + 1) / N
        point_y = F_orig**n
        if point_y < y_min:
            continue
        # B exact-bootstrap draws of F_chunk(x_i); transform to file CDF.
        boots = sorted((rng.binomialvariate(N, F_orig) / N) ** n for _ in range(B))
        lo_y = max(y_min, boots[lo_q_idx])
        hi_y = min(1.0, boots[hi_q_idx])
        band.append((x_data, lo_y, hi_y, point_y))

    if not band:
        parts.append("</svg>")
        out_path.write_text("\n".join(parts))
        return

    # Anchor the band/curve at the visible bottom-left.
    anchor_x = x_min if y_min == 0.0 else band[0][0]
    right_y_lo = band[-1][1] if truncated else 1.0
    right_y_hi = band[-1][2] if truncated else 1.0
    right_y_pt = band[-1][3] if truncated else 1.0

    # CI band: a polygon fill + explicit thin polylines on the upper and lower
    # edges. The edge lines stay visible even when the band is sub-pixel-wide
    # (which happens at large M, where the CI is genuinely narrow). The fill
    # adds a soft "this is the same region" cue between the edges.
    upper = [(x_to_px(anchor_x), y_to_px(y_min))]
    lower = [(x_to_px(anchor_x), y_to_px(y_min))]
    for x, lo_y, hi_y, _ in band:
        upper.append((x_to_px(x), y_to_px(hi_y)))
        lower.append((x_to_px(x), y_to_px(lo_y)))
    upper.append((x_to_px(x_max), y_to_px(right_y_hi)))
    lower.append((x_to_px(x_max), y_to_px(right_y_lo)))
    polygon_pts = upper + list(reversed(lower))
    poly_str = " ".join(f"{x:.2f},{y:.2f}" for x, y in polygon_pts)
    parts.append(
        f'<polygon points="{poly_str}" fill="{color}" fill-opacity="0.35" '
        f'stroke="none"/>'
    )
    upper_str = " ".join(f"{x:.2f},{y:.2f}" for x, y in upper)
    lower_str = " ".join(f"{x:.2f},{y:.2f}" for x, y in lower)
    parts.append(
        f'<polyline points="{upper_str}" fill="none" stroke="{color}" '
        f'stroke-width="0.9" stroke-opacity="0.85"/>'
    )
    parts.append(
        f'<polyline points="{lower_str}" fill="none" stroke="{color}" '
        f'stroke-width="0.9" stroke-opacity="0.85"/>'
    )

    # Point-estimate curve, drawn on top so it remains the focal element.
    curve = [(x_to_px(anchor_x), y_to_px(y_min))]
    for x, _, _, point_y in band:
        curve.append((x_to_px(x), y_to_px(max(y_min, point_y))))
    curve.append((x_to_px(x_max), y_to_px(right_y_pt)))
    polyline = " ".join(f"{x:.2f},{y:.2f}" for x, y in curve)
    parts.append(
        f'<polyline points="{polyline}" fill="none" stroke="{color}" '
        f'stroke-width="2.0"/>'
    )

    # n = X label box (lower-left, matches main-plot's legend style).
    label_x = margin_left + 12
    label_y = margin_top + plot_h - 12
    parts.append(
        f'<rect x="{label_x - 6}" y="{label_y - 14}" width="90" height="20" '
        f'fill="white" fill-opacity="0.85" stroke="#888"/>'
    )
    parts.append(
        f'<text x="{label_x}" y="{label_y}" font-weight="bold" fill="{color}">'
        f"n = {n}</text>"
    )

    parts.append("</svg>")
    out_path.write_text("\n".join(parts))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "config",
        nargs="?",
        default=str(REPO_ROOT / "inputs.yaml"),
        help="YAML config (default: repo inputs.yaml)",
    )
    ap.add_argument(
        "-o",
        "--output",
        default="chunking.svg",
        help="Output SVG path (default: chunking.svg)",
    )
    ap.add_argument(
        "--ns", default="1,2,4,8,16,32", help="Comma-separated list of n values to plot"
    )
    ap.add_argument(
        "--runs",
        type=int,
        default=50_000,
        help="Monte Carlo trials per n (default: 50000)",
    )
    ap.add_argument(
        "--scenario",
        choices=("optimistic", "realistic"),
        default="optimistic",
        help="Per-chunk bandwidth model",
    )
    ap.add_argument(
        "--xmax",
        type=float,
        default=None,
        help="Truncate the x-axis at this time in seconds "
        "(curves continue off-frame). "
        "Default: 0.5 s past where the slowest curve crosses P99.",
    )
    ap.add_argument(
        "--cdfmin",
        type=float,
        default=0.0,
        help="Lower bound of the y-axis (cumulative probability) in [0, 1). "
        "Use e.g. --cdfmin 0.9 to zoom into the top decile where curves "
        "cross P99. Default: 0.",
    )
    ap.add_argument(
        "--ci",
        action="store_true",
        help="Additionally emit one per-n SVG with a pointwise bootstrap "
        "CI band around that single curve. Main multi-curve plot is "
        "still written. Output names: <stem>-n<NN>.svg.",
    )
    ap.add_argument(
        "--ci-runs",
        type=int,
        default=500,
        help="Bootstrap resamples per x-position for --ci (default: 500)",
    )
    ap.add_argument(
        "--ci-alpha",
        type=float,
        default=0.05,
        help="Significance level for --ci bands; 0.05 → 95%% CI (default).",
    )
    args = ap.parse_args()
    if not 0.0 <= args.cdfmin < 1.0:
        ap.error("--cdfmin must be in [0, 1)")
    if not 0.0 < args.ci_alpha < 1.0:
        ap.error("--ci-alpha must be in (0, 1)")

    base = estimator.load_config(Path(args.config), None)
    base.monte_carlo_runs = args.runs
    ns = [int(s) for s in args.ns.split(",")]

    curves: list[tuple[int, list[float]]] = []
    for n in ns:
        print(f"  simulating n={n} ...", file=sys.stderr, flush=True)
        curves.append((n, simulate_chunk(base, n, args.scenario)))

    # Single x_max shared across the main plot and the per-n CI plots, so the
    # latter can be visually compared back to the multi-curve overview.
    x_max = compute_x_max(curves, args.xmax)

    out_path = Path(args.output)
    render(
        curves, base, args.scenario, out_path, x_max_override=x_max, y_min=args.cdfmin
    )
    print(f"Wrote {out_path.resolve()}")

    if args.ci:
        for idx, (n, sorted_times) in enumerate(curves):
            color = PALETTE[idx % len(PALETTE)]
            ci_path = out_path.with_stem(f"{out_path.stem}-n{n:02d}")
            print(f"  bootstrapping CI for n={n} ...", file=sys.stderr, flush=True)
            render_ci(
                n,
                sorted_times,
                color,
                base,
                args.scenario,
                ci_path,
                x_max=x_max,
                y_min=args.cdfmin,
                B=args.ci_runs,
                alpha=args.ci_alpha,
            )
            print(f"Wrote {ci_path.resolve()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
