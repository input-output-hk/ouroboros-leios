#!/usr/bin/env python3
"""Estimate Monte Carlo noise in chunking file-P99 estimates by reseed.

For each n in --ns, runs the chunk-size Monte Carlo K times with different
RNG seeds (each at --runs trials), computes the implied whole-file P99
( = chunk's quantile-at-0.99^(1/n) ) per seed, and reports per-n
mean / std / range / coefficient of variation.

A high coefficient of variation (CoV) flags an unreliable estimate; the
chunking plot at that n shouldn't be trusted without bumping --runs.

Usage:
  tools/chunking_stability.py [config.yaml] [--ns 1,2,4,8,16,32]
                              [--seeds 10] [--runs 50000]
                              [--scenario optimistic|realistic]
"""
from __future__ import annotations

import argparse
import dataclasses
import math
import statistics
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))
import estimator  # noqa: E402


def _bdp_ssthresh(link_mbps: float, rtt_s: float, mss: int) -> float:
    return max(1.0, math.floor(link_mbps * 1e6 * rtt_s / 8.0 / mss))


def run_chunk(
    base: estimator.Config, n: int, scenario: str, seed: int, runs: int
) -> list[float]:
    chunk_kb = base.file_size_kb / n
    link = (
        base.link_speed_mbps if scenario == "optimistic" else base.link_speed_mbps / n
    )
    cfg = dataclasses.replace(
        base,
        file_size_kb=chunk_kb,
        link_speed_mbps=link,
        initial_ssthresh_segs=_bdp_ssthresh(link, base.rtt_s, base.mss_bytes),
        monte_carlo_runs=runs,
        random_seed=seed,
    )
    return sorted(estimator.monte_carlo(cfg))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "config",
        nargs="?",
        default=str(REPO_ROOT / "inputs.yaml"),
        help="YAML config (default: repo inputs.yaml)",
    )
    ap.add_argument(
        "--ns", default="1,2,4,8,16,32", help="Comma-separated list of n values to test"
    )
    ap.add_argument(
        "--seeds",
        type=int,
        default=10,
        help="Number of independent reseeds per n (default: 10)",
    )
    ap.add_argument(
        "--runs",
        type=int,
        default=50_000,
        help="Monte Carlo trials per (n, seed) (default: 50000)",
    )
    ap.add_argument(
        "--scenario",
        choices=("optimistic", "realistic"),
        default="optimistic",
        help="Per-chunk bandwidth model",
    )
    args = ap.parse_args()

    base = estimator.load_config(Path(args.config), None)
    ns = [int(s) for s in args.ns.split(",")]

    print(
        f"# Stability check: {args.seeds} seeds × M={args.runs:,} per n, "
        f"scenario={args.scenario}"
    )
    print(
        f"#   size={base.file_size_kb:g} kB, link={base.link_speed_mbps:g} Mbps, "
        f"RTT={base.rtt_ms:g} ms, p_eff={base.effective_loss_rate():.2e}"
    )
    print()
    header = (
        f"{'n':>3} {'q':>10} {'mean P99':>10} {'std':>9} "
        f"{'range':>22} {'CoV':>7}  verdict"
    )
    print(header)
    print("-" * len(header))

    for n in ns:
        q = 0.99 ** (1.0 / n)
        ests = []
        for seed in range(args.seeds):
            ch = run_chunk(base, n, args.scenario, seed, args.runs)
            ests.append(estimator.percentile_of(ch, q))
        mean = statistics.mean(ests)
        std = statistics.stdev(ests) if len(ests) > 1 else 0.0
        cov = (std / mean * 100) if mean > 0 else float("inf")
        if cov < 2.0:
            verdict = "stable"
        elif cov < 5.0:
            verdict = "ok"
        elif cov < 10.0:
            verdict = "noisy — bump --runs"
        else:
            verdict = "UNSTABLE — bump --runs or investigate CDF step"
        print(
            f"{n:>3} {q:>10.6f} {mean:>9.3f}s {std:>8.3f}s "
            f"[{min(ests):>6.3f}, {max(ests):>6.3f}]s {cov:>6.1f}%  {verdict}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
