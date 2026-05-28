#!/usr/bin/env python3
"""
Estimate the time to download a file over TCP CUBIC, including random loss.

Models slow start (with HyStart ssthresh as input), CUBIC concave/convex
congestion avoidance, multiplicative decrease on loss, and an optional
Gilbert-Elliott bursty-loss model alongside the default Bernoulli loss.

Runs a Monte Carlo and reports a percentile of the download-time CDF, plus
an SVG plot. See inputs.yaml for the configuration schema.
"""

from __future__ import annotations

import argparse
import math
import random
import statistics
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

import yaml


# --------------------------------------------------------------------------- #
# Config                                                                      #
# --------------------------------------------------------------------------- #


@dataclass
class Config:
    link_speed_mbps: float
    file_size_kb: float
    rtt_ms: float
    initial_ssthresh_segs: float
    percentile: float
    monte_carlo_runs: int

    mss_bytes: int
    initial_cwnd_segs: float
    cubic_c: float
    cubic_beta: float
    fast_convergence: bool

    loss_model: str  # "bernoulli" | "gilbert_elliott"
    p_bernoulli: float
    p_good: float
    p_bad: float
    p_g2b: float
    p_b2g: float
    ge_start_state: str

    # Per-round RTT jitter. "none" disables it (RTT = rtt_ms every round).
    # "lognormal" multiplies rtt_ms by exp(N(0, sigma)) — natural for RTT,
    # always positive and right-skewed. "normal" and "uniform" provided as
    # alternatives; all are clamped to >= 1ms.
    jitter_model: str  # "none" | "lognormal" | "normal" | "uniform"
    jitter_sigma: float  # for lognormal
    jitter_std_ms: float  # for normal
    jitter_half_range_ms: float  # for uniform

    random_seed: Optional[int]
    svg_path: str
    ssthresh_auto: bool = False

    @property
    def rtt_s(self) -> float:
        return self.rtt_ms / 1000.0

    @property
    def link_bps(self) -> float:
        return self.link_speed_mbps * 1e6

    @property
    def file_bytes(self) -> int:
        return int(round(self.file_size_kb * 1000))

    @property
    def bdp_cap_segs(self) -> int:
        return max(1, math.floor(self.link_bps * self.rtt_s / 8.0 / self.mss_bytes))

    def ge_effective_p(self) -> float:
        denom = self.p_g2b + self.p_b2g
        if denom <= 0:
            return self.p_good if self.ge_start_state == "good" else self.p_bad
        pi_good = self.p_b2g / denom
        pi_bad = self.p_g2b / denom
        return pi_good * self.p_good + pi_bad * self.p_bad

    def effective_loss_rate(self) -> float:
        return (
            self.p_bernoulli
            if self.loss_model == "bernoulli"
            else self.ge_effective_p()
        )

    def steady_state_avg_cwnd_segs(self) -> float:
        # Ha, Rhee, Xu 2008, eq. (5): E{W_cubic} = ((C(4-β))/(4β))^(1/4) * (RTT/p)^(3/4).
        p = self.effective_loss_rate()
        if p <= 0:
            return float("inf")
        coef = (self.cubic_c * (4 - self.cubic_beta) / (4 * self.cubic_beta)) ** 0.25
        return coef * (self.rtt_s / p) ** 0.75

    def steady_state_throughput_bps(self) -> float:
        w = self.steady_state_avg_cwnd_segs()
        if math.isinf(w):
            return self.link_bps
        return w * self.mss_bytes * 8.0 / self.rtt_s


def load_config(path: Path, percentile_override: Optional[float]) -> Config:
    try:
        with path.open("r") as f:
            raw = yaml.safe_load(f)
    except FileNotFoundError:
        sys.exit(f"error: config file not found: {path}")
    except OSError as e:
        sys.exit(f"error: could not read {path}: {e}")
    except yaml.YAMLError as e:
        sys.exit(f"error: invalid YAML in {path}: {e}")

    if not isinstance(raw, dict):
        sys.exit(f"error: top level of {path} must be a mapping")

    def req(d: dict, key: str, path_str: str):
        if key not in d:
            sys.exit(f"error: missing required field '{path_str}' in {path}")
        return d[key]

    tcp = raw.get("tcp", {}) or {}
    loss = raw.get("loss", {}) or {}
    bern = loss.get("bernoulli", {}) or {}
    ge = loss.get("gilbert_elliott", {}) or {}
    jitter = raw.get("rtt_jitter", {}) or {}
    jln = jitter.get("lognormal", {}) or {}
    jnm = jitter.get("normal", {}) or {}
    jun = jitter.get("uniform", {}) or {}
    out = raw.get("output", {}) or {}

    jitter_model = jitter.get("model", "lognormal")
    if jitter_model not in ("none", "lognormal", "normal", "uniform"):
        sys.exit(
            f"error: rtt_jitter.model must be 'none', 'lognormal', 'normal', or 'uniform', got {jitter_model!r}"
        )

    percentile = (
        percentile_override
        if percentile_override is not None
        else float(req(raw, "percentile", "percentile"))
    )
    if not 0 < percentile < 1:
        sys.exit(f"error: percentile must be in (0, 1), got {percentile}")

    loss_model = loss.get("model", "bernoulli")
    if loss_model not in ("bernoulli", "gilbert_elliott"):
        sys.exit(
            f"error: loss.model must be 'bernoulli' or 'gilbert_elliott', got {loss_model!r}"
        )

    ge_start_state = ge.get("start_state", "good")
    if ge_start_state not in ("good", "bad"):
        sys.exit(
            f"error: loss.gilbert_elliott.start_state must be 'good' or 'bad', got {ge_start_state!r}"
        )

    link_speed_mbps = float(req(raw, "link_speed_mbps", "link_speed_mbps"))
    rtt_ms = float(req(raw, "rtt_ms", "rtt_ms"))
    mss_bytes = int(tcp.get("mss_bytes", 1460))

    # initial_ssthresh_segs is optional: defaults to the link BDP, which models
    # HyStart firing right at link saturation (the ideal Linux/CUBIC behavior on
    # a clean path). Users wanting a more conservative HyStart can set it explicitly.
    if "initial_ssthresh_segs" in raw and raw["initial_ssthresh_segs"] is not None:
        initial_ssthresh_segs = float(raw["initial_ssthresh_segs"])
        ssthresh_auto = False
    else:
        link_bps = link_speed_mbps * 1e6
        rtt_s = rtt_ms / 1000.0
        initial_ssthresh_segs = max(1.0, math.floor(link_bps * rtt_s / 8.0 / mss_bytes))
        ssthresh_auto = True

    return Config(
        link_speed_mbps=link_speed_mbps,
        file_size_kb=float(req(raw, "file_size_kb", "file_size_kb")),
        rtt_ms=rtt_ms,
        initial_ssthresh_segs=initial_ssthresh_segs,
        percentile=percentile,
        monte_carlo_runs=int(raw.get("monte_carlo_runs", 1000)),
        mss_bytes=mss_bytes,
        initial_cwnd_segs=float(tcp.get("initial_cwnd_segs", 10)),
        cubic_c=float(tcp.get("cubic_c", 0.4)),
        cubic_beta=float(tcp.get("cubic_beta", 0.3)),
        fast_convergence=bool(tcp.get("fast_convergence", True)),
        loss_model=loss_model,
        p_bernoulli=float(bern.get("p", 0.0)),
        p_good=float(ge.get("p_good", 0.0)),
        p_bad=float(ge.get("p_bad", 0.0)),
        p_g2b=float(ge.get("p_good_to_bad", 0.0)),
        p_b2g=float(ge.get("p_bad_to_good", 0.0)),
        ge_start_state=ge_start_state,
        jitter_model=jitter_model,
        jitter_sigma=float(jln.get("sigma", 0.15)),
        jitter_std_ms=float(jnm.get("std_ms", 5.0)),
        jitter_half_range_ms=float(jun.get("half_range_ms", 10.0)),
        random_seed=raw.get("random_seed"),
        svg_path=str(out.get("svg_path", "cdf.svg")),
        ssthresh_auto=ssthresh_auto,
    )


# --------------------------------------------------------------------------- #
# Simulation core                                                             #
# --------------------------------------------------------------------------- #


def _sample_rtt(cfg: Config, rng: random.Random) -> float:
    rtt = cfg.rtt_s
    if cfg.jitter_model == "none":
        return rtt
    if cfg.jitter_model == "lognormal":
        return max(0.001, rtt * math.exp(rng.gauss(0.0, cfg.jitter_sigma)))
    if cfg.jitter_model == "normal":
        return max(0.001, rng.gauss(rtt, cfg.jitter_std_ms / 1000.0))
    if cfg.jitter_model == "uniform":
        half = cfg.jitter_half_range_ms / 1000.0
        return max(0.001, rtt + rng.uniform(-half, half))
    return rtt


def _sample_round_loss_bernoulli(packets: int, p: float, rng: random.Random) -> bool:
    if p <= 0 or packets <= 0:
        return False
    if p >= 1:
        return True
    no_loss_prob = (1.0 - p) ** packets
    return rng.random() > no_loss_prob


def _sample_round_loss_ge(
    packets: int,
    state: str,
    cfg: Config,
    rng: random.Random,
) -> tuple[bool, str]:
    # Evolves Gilbert-Elliott state per packet; returns (any-loss, new-state).
    lost = False
    for _ in range(packets):
        if state == "good":
            if rng.random() < cfg.p_good:
                lost = True
            if rng.random() < cfg.p_g2b:
                state = "bad"
        else:
            if rng.random() < cfg.p_bad:
                lost = True
            if rng.random() < cfg.p_b2g:
                state = "good"
    return lost, state


def simulate_one_run(cfg: Config, rng: random.Random) -> float:
    """One Monte Carlo trial. Returns total download time in seconds."""
    file_bytes = cfg.file_bytes
    if file_bytes <= 0:
        return 0.0

    mss = cfg.mss_bytes
    bdp_cap = cfg.bdp_cap_segs
    ssthresh = cfg.initial_ssthresh_segs
    beta = cfg.cubic_beta
    C = cfg.cubic_c

    cwnd = float(cfg.initial_cwnd_segs)
    bytes_sent = 0
    t_seconds = 0.0

    phase = "slow_start"
    W_max = 0.0
    last_W_max = 0.0
    K = 0.0
    cubic_origin = 0.0
    # Wall-clock seconds elapsed since CA started (loss event or clean ss-exit).
    # Replaces the round-count-times-nominal-RTT used previously; required so the
    # CUBIC formula sees real elapsed time when RTT jitter is enabled.
    ca_elapsed_s = 0.0

    ge_state = cfg.ge_start_state

    # Safety cap to prevent infinite loops on pathological inputs.
    max_rounds = 10_000_000
    rounds = 0

    while bytes_sent < file_bytes:
        rounds += 1
        if rounds > max_rounds:
            return float("inf")

        eff_cwnd = max(1, min(int(cwnd), bdp_cap))
        remaining_bytes = file_bytes - bytes_sent
        remaining_packets = (remaining_bytes + mss - 1) // mss
        packets_attempted = min(eff_cwnd, remaining_packets)

        if cfg.loss_model == "bernoulli":
            lost = _sample_round_loss_bernoulli(packets_attempted, cfg.p_bernoulli, rng)
        else:
            lost, ge_state = _sample_round_loss_ge(
                packets_attempted, ge_state, cfg, rng
            )

        sampled_rtt = _sample_rtt(cfg, rng)

        # All packets in cwnd are treated as eventually delivered (TCP retransmits
        # cover gaps); the loss event reshapes cwnd for the *next* round.
        bytes_sent = min(file_bytes, bytes_sent + packets_attempted * mss)
        t_seconds += sampled_rtt
        if phase == "ca":
            ca_elapsed_s += sampled_rtt

        if bytes_sent >= file_bytes:
            break

        if lost:
            cwnd_at_loss = float(eff_cwnd)
            # Fast convergence (Ha 2008 §3.7): if this loss happened below the previous
            # W_max, reduce W_max further before applying the cwnd cut, releasing
            # bandwidth to hypothetical new flows. We track last_W_max regardless.
            if cfg.fast_convergence and last_W_max > 0 and cwnd_at_loss < last_W_max:
                W_max = cwnd_at_loss * (2.0 - beta) / 2.0
            else:
                W_max = cwnd_at_loss
            last_W_max = max(last_W_max, W_max)
            cwnd = max(1.0, cwnd_at_loss * (1.0 - beta))
            K = (W_max * beta / C) ** (1.0 / 3.0)
            cubic_origin = W_max
            ca_elapsed_s = 0.0
            phase = "ca"
        else:
            if phase == "slow_start":
                cwnd *= 2.0
                if cwnd >= ssthresh:
                    cwnd = ssthresh
                    # Algorithm 2 of De Silva et al.: after a clean slow-start exit,
                    # CUBIC starts CA already at the plateau (K=0, origin=W_s),
                    # so the cubic immediately enters its convex region.
                    W_max = ssthresh
                    last_W_max = ssthresh
                    K = 0.0
                    cubic_origin = W_max
                    ca_elapsed_s = 0.0
                    phase = "ca"
            else:
                cwnd = max(1.0, C * (ca_elapsed_s - K) ** 3 + cubic_origin)

    return t_seconds


def monte_carlo(cfg: Config) -> list[float]:
    rng = random.Random(cfg.random_seed)
    return [simulate_one_run(cfg, rng) for _ in range(cfg.monte_carlo_runs)]


def percentile_of(sorted_times: list[float], q: float) -> float:
    if not sorted_times:
        return float("nan")
    n = len(sorted_times)
    # Type 7 / linear interpolation, matching numpy.percentile default.
    h = (n - 1) * q
    lo = int(math.floor(h))
    hi = int(math.ceil(h))
    if lo == hi:
        return sorted_times[lo]
    return sorted_times[lo] + (h - lo) * (sorted_times[hi] - sorted_times[lo])


# --------------------------------------------------------------------------- #
# SVG plotting (hand-rolled, no matplotlib)                                   #
# --------------------------------------------------------------------------- #


def render_cdf_svg(
    sorted_times: list[float],
    markers: list[tuple[float, float, str]],
    cfg: Config,
    out_path: Path,
) -> None:
    # markers: list of (q, time, color). The first marker is treated as the
    # primary answer (bold label, "P{q} = ... s **"-style emphasis); any further
    # markers are drawn as secondary references with thinner styling.
    width = 880
    height = 540
    margin_left = 80
    margin_right = 30
    margin_top = 70  # room for title + two subtitle lines above the plot
    margin_bottom = 60
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom

    finite = [t for t in sorted_times if math.isfinite(t)]
    if not finite:
        x_min, x_max = 0.0, 1.0
    else:
        x_min = 0.0
        x_max = finite[-1]
        if x_max <= x_min:
            x_max = x_min + 1.0
        # Add ~5% headroom so the last step doesn't sit on the edge.
        x_max *= 1.05

    n = len(sorted_times)

    def x_to_px(x: float) -> float:
        return margin_left + (x - x_min) / (x_max - x_min) * plot_w

    def y_to_px(y: float) -> float:
        return margin_top + (1.0 - y) * plot_h

    # Step polyline for empirical CDF.
    pts: list[tuple[float, float]] = [(x_to_px(x_min), y_to_px(0.0))]
    for i, t in enumerate(sorted_times):
        y_before = i / n
        y_after = (i + 1) / n
        if math.isfinite(t):
            px = x_to_px(t)
            pts.append((px, y_to_px(y_before)))
            pts.append((px, y_to_px(y_after)))
    pts.append((x_to_px(x_max), y_to_px(1.0)))

    polyline = " ".join(f"{x:.2f},{y:.2f}" for x, y in pts)

    # Axis ticks.
    n_x_ticks = 8
    n_y_ticks = 10
    x_ticks = [x_min + (x_max - x_min) * i / n_x_ticks for i in range(n_x_ticks + 1)]
    y_ticks = [i / n_y_ticks for i in range(n_y_ticks + 1)]

    def fmt_x(v: float) -> str:
        if v >= 100:
            return f"{v:.0f}"
        if v >= 10:
            return f"{v:.1f}"
        if v >= 1:
            return f"{v:.2f}"
        return f"{v:.3f}"

    parts: list[str] = []
    parts.append(
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" '
        f'font-family="Helvetica, Arial, sans-serif" font-size="12">'
    )
    parts.append('<rect width="100%" height="100%" fill="white"/>')

    parts.append(
        f'<text x="{width/2:.1f}" y="22" text-anchor="middle" font-size="16" '
        f'font-weight="bold">TCP CUBIC short-flow download-time CDF</text>'
    )
    if cfg.jitter_model == "none":
        jitter_short = "none"
    elif cfg.jitter_model == "lognormal":
        jitter_short = f"lognormal(σ={cfg.jitter_sigma:g})"
    elif cfg.jitter_model == "normal":
        jitter_short = f"normal(std={cfg.jitter_std_ms:g}ms)"
    else:
        jitter_short = f"uniform(±{cfg.jitter_half_range_ms:g}ms)"
    subtitle_l1 = (
        f"size={cfg.file_size_kb:g} kB, link={cfg.link_speed_mbps:g} Mbps, "
        f"RTT={cfg.rtt_ms:g} ms"
    )
    subtitle_l2 = (
        f"loss={cfg.loss_model} (p_eff={cfg.effective_loss_rate():.2e}), "
        f"jitter={jitter_short}, runs={cfg.monte_carlo_runs}"
    )
    parts.append(
        f'<text x="{width/2:.1f}" y="40" text-anchor="middle" fill="#555">{subtitle_l1}</text>'
    )
    parts.append(
        f'<text x="{width/2:.1f}" y="56" text-anchor="middle" fill="#555">{subtitle_l2}</text>'
    )

    # Plot area background.
    parts.append(
        f'<rect x="{margin_left}" y="{margin_top}" '
        f'width="{plot_w}" height="{plot_h}" fill="#fafafa" stroke="#888"/>'
    )

    # Grid + tick labels.
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
            f'text-anchor="end" fill="#333">{tv:.1f}</text>'
        )

    # Axis labels.
    parts.append(
        f'<text x="{margin_left + plot_w/2:.1f}" y="{height - 15}" '
        f'text-anchor="middle">Download time (seconds)</text>'
    )
    parts.append(
        f'<text transform="translate(20,{margin_top + plot_h/2:.1f}) rotate(-90)" '
        f'text-anchor="middle">Cumulative probability</text>'
    )

    # CDF curve.
    parts.append(
        f'<polyline points="{polyline}" fill="none" stroke="#1f77b4" stroke-width="1.8"/>'
    )

    # Percentile markers. Labels go to the bottom of the plot (above the x-axis)
    # so they never collide with the title/subtitle area, and so multiple markers
    # can stack neatly regardless of where their dots fall in the plot.
    line_h = 16
    label_row_base = margin_top + plot_h - 8  # bottom-most row, just inside plot
    for idx, (q, t, color) in enumerate(markers):
        if not math.isfinite(t):
            continue
        primary = idx == 0
        stroke_w = 1.8 if primary else 1.3
        dash = "7,4" if primary else "4,3"
        radius = 4 if primary else 3
        font_weight = "bold" if primary else "normal"

        px = x_to_px(t)
        py = y_to_px(q)
        parts.append(
            f'<line x1="{px:.2f}" y1="{margin_top}" x2="{px:.2f}" '
            f'y2="{margin_top + plot_h}" stroke="{color}" '
            f'stroke-width="{stroke_w}" stroke-dasharray="{dash}"/>'
        )
        parts.append(
            f'<line x1="{margin_left}" y1="{py:.2f}" '
            f'x2="{margin_left + plot_w}" y2="{py:.2f}" stroke="{color}" '
            f'stroke-width="{stroke_w}" stroke-dasharray="{dash}"/>'
        )
        parts.append(
            f'<circle cx="{px:.2f}" cy="{py:.2f}" r="{radius}" fill="{color}"/>'
        )

        label = f"P{q*100:g} = {t:.3f} s"
        label_y = label_row_base - idx * line_h
        anchor = "start" if px < margin_left + plot_w * 0.7 else "end"
        dx = 8 if anchor == "start" else -8
        # White stroke "halo" + colored fill via paint-order: keeps the label
        # readable even where the dashed line passes through the text.
        parts.append(
            f'<text x="{px + dx:.2f}" y="{label_y:.2f}" text-anchor="{anchor}" '
            f'fill="{color}" font-weight="{font_weight}" stroke="white" '
            f'stroke-width="3" paint-order="stroke fill">{label}</text>'
        )

    parts.append("</svg>")
    out_path.write_text("\n".join(parts))


# --------------------------------------------------------------------------- #
# Reporting                                                                   #
# --------------------------------------------------------------------------- #


def print_report(
    cfg: Config, times: list[float], sorted_times: list[float], percentile_time: float
) -> None:
    finite = [t for t in times if math.isfinite(t)]
    p_eff = cfg.effective_loss_rate()
    bdp_segs = cfg.bdp_cap_segs
    bdp_thp_bps = bdp_segs * cfg.mss_bytes * 8.0 / cfg.rtt_s
    ss_w = cfg.steady_state_avg_cwnd_segs()
    ss_thp_bps = cfg.steady_state_throughput_bps()

    def fmt_bps(b: float) -> str:
        if not math.isfinite(b):
            return "inf"
        return f"{b/1e6:.2f} Mbps"

    print("== TCP CUBIC download-time estimator ==")
    print(f"File size            : {cfg.file_size_kb:g} kB ({cfg.file_bytes} B)")
    print(f"Link cap             : {cfg.link_speed_mbps:g} Mbps")
    print(f"RTT                  : {cfg.rtt_ms:g} ms")
    print(f"MSS                  : {cfg.mss_bytes} B")
    print(f"Initial cwnd W0      : {cfg.initial_cwnd_segs:g} segs")
    ssthresh_note = "  (auto-defaulted to link BDP)" if cfg.ssthresh_auto else ""
    print(f"Initial ssthresh Ws  : {cfg.initial_ssthresh_segs:g} segs{ssthresh_note}")
    print(f"CUBIC C, beta        : {cfg.cubic_c}, {cfg.cubic_beta}")
    print(f"Fast convergence     : {cfg.fast_convergence}")
    print(f"Loss model           : {cfg.loss_model} (p_eff = {p_eff:.3e})")
    if cfg.jitter_model == "none":
        jitter_desc = "none"
    elif cfg.jitter_model == "lognormal":
        jitter_desc = f"lognormal (sigma={cfg.jitter_sigma:g})"
    elif cfg.jitter_model == "normal":
        jitter_desc = f"normal (std={cfg.jitter_std_ms:g} ms)"
    else:
        jitter_desc = f"uniform (±{cfg.jitter_half_range_ms:g} ms)"
    print(f"RTT jitter           : {jitter_desc}")
    print(f"Monte Carlo runs     : {cfg.monte_carlo_runs}")
    print()
    print("-- Diagnostics --")
    print(f"BDP cap              : {bdp_segs} segs  ->  {fmt_bps(bdp_thp_bps)} ceiling")
    print(
        f"Steady-state E[Wcubic] (Ha 2008 eq.5): {ss_w:.1f} segs  ->  {fmt_bps(ss_thp_bps)}"
    )
    print(
        "  (Diagnostic only; the simulation enforces only the BDP cap. If the steady-state"
    )
    print(
        "   throughput above is well below the BDP cap, loss is the binding constraint.)"
    )
    print()
    print("-- Results --")
    if not finite:
        print("(no completed runs — check inputs)")
        return
    avg_thp_bps = (cfg.file_bytes * 8.0) / statistics.mean(finite)
    print(f"Completed runs       : {len(finite)} / {cfg.monte_carlo_runs}")
    print(f"min  time            : {min(finite):.4f} s")
    print(
        f"mean time            : {statistics.mean(finite):.4f} s   "
        f"(=> mean throughput {fmt_bps(avg_thp_bps)})"
    )
    print(f"median time          : {statistics.median(finite):.4f} s")
    print(f"max  time            : {max(finite):.4f} s")
    print(f"stdev                : {statistics.pstdev(finite):.4f} s")
    print()
    quartiles = [0.10, 0.25, 0.50, 0.75, 0.90, 0.95, 0.99]
    print("Percentiles:")
    for q in quartiles:
        print(
            f"  P{int(q*100):>2d}              : {percentile_of(sorted_times, q):.4f} s"
        )
    print()
    print(f"** P{cfg.percentile*100:g} download time: {percentile_time:.4f} s **")


# --------------------------------------------------------------------------- #
# CLI                                                                         #
# --------------------------------------------------------------------------- #


def main() -> int:
    parser = argparse.ArgumentParser(
        prog="estimator",
        description="TCP CUBIC short-flow download-time estimator with random loss.",
    )
    parser.add_argument(
        "config",
        nargs="?",
        default="inputs.yaml",
        help="YAML config file (default: inputs.yaml)",
    )
    parser.add_argument(
        "-p",
        "--percentile",
        type=float,
        default=None,
        help="Percentile in (0,1); overrides the YAML value",
    )
    args = parser.parse_args()

    cfg = load_config(Path(args.config), args.percentile)
    times = monte_carlo(cfg)
    sorted_times = sorted(times)
    percentile_time = percentile_of(sorted_times, cfg.percentile)

    print_report(cfg, times, sorted_times, percentile_time)

    # Always show the requested percentile; add P99 as a tail-reference marker
    # unless the requested percentile already meets or exceeds P99.
    markers: list[tuple[float, float, str]] = [
        (cfg.percentile, percentile_time, "#d62728")
    ]
    if cfg.percentile < 0.99:
        markers.append((0.99, percentile_of(sorted_times, 0.99), "#9467bd"))

    out_path = Path(cfg.svg_path)
    render_cdf_svg(sorted_times, markers, cfg, out_path)
    print(f"\nCDF plot written to: {out_path.resolve()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
