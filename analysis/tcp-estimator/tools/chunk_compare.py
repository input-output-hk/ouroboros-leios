#!/usr/bin/env python3
"""Compare single-shot vs n-chunk parallel download P99 for the configured workload.

For each n, evaluates two scenarios:
  (a) Optimistic: each chunk gets the full link (distinct peers, no shared
      bottleneck). Overstates the benefit but is the upper bound.
  (b) Realistic: client-downlink shared, so each parallel chunk effectively
      sees link/n bandwidth (and BDP/n in segments).

Under parallel chunking the whole-file time is max(T_1, ..., T_n), so the file's
P99 sits at the chunk distribution's quantile-at-0.99^(1/n). See
notes/parallel-chunking.md for the math.

Usage:
  tools/chunk_compare.py [inputs.yaml]
"""
from __future__ import annotations

import dataclasses
import math
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))
import estimator  # noqa: E402


def _bdp_ssthresh(link_mbps: float, rtt_s: float, mss: int) -> float:
    return max(1.0, math.floor(link_mbps * 1e6 * rtt_s / 8.0 / mss))


def run_at(base: estimator.Config, file_kb: float, link_mbps: float) -> list[float]:
    cfg = dataclasses.replace(
        base,
        file_size_kb=file_kb,
        link_speed_mbps=link_mbps,
        initial_ssthresh_segs=_bdp_ssthresh(link_mbps, base.rtt_s, base.mss_bytes),
    )
    return sorted(estimator.monte_carlo(cfg))


def main() -> int:
    config_path = Path(sys.argv[1]) if len(sys.argv) > 1 else REPO_ROOT / "inputs.yaml"
    base = estimator.load_config(config_path, None)
    base.monte_carlo_runs = 50_000  # tail stability at q^(1/n) up to ~0.9999

    whole_kb = base.file_size_kb
    whole_mbps = base.link_speed_mbps

    print(
        f"# Comparison config: size={whole_kb:g} kB, link={whole_mbps:g} Mbps, "
        f"RTT={base.rtt_ms:g} ms, p={base.p_bernoulli:g}, MC={base.monte_carlo_runs}"
    )
    print()

    sorted_whole = run_at(base, whole_kb, whole_mbps)
    p99_baseline = estimator.percentile_of(sorted_whole, 0.99)
    p95_baseline = estimator.percentile_of(sorted_whole, 0.95)
    p50_baseline = estimator.percentile_of(sorted_whole, 0.50)
    print("Baseline (n=1, no chunking, full link):")
    print(
        f"  P50 = {p50_baseline:.3f}s   P95 = {p95_baseline:.3f}s   P99 = {p99_baseline:.3f}s"
    )
    print()

    header = f"{'n':>3}  {'chunk':>8}  {'link/ch':>9}  {'P99_chunk':>10}  {'file_P99':>10}  {'vs base':>9}"

    def sweep(title: str, link_for_n):
        print(title)
        print(header)
        print("-" * len(header))
        for n in (2, 4, 8, 16, 32):
            chunk_kb = whole_kb / n
            link_per_chunk = link_for_n(n)
            sorted_chunk = run_at(base, chunk_kb, link_per_chunk)
            p99_chunk = estimator.percentile_of(sorted_chunk, 0.99)
            q = 0.99 ** (1.0 / n)
            p99_file = estimator.percentile_of(sorted_chunk, q)
            delta = (p99_file / p99_baseline - 1.0) * 100
            print(
                f"{n:>3}  {chunk_kb:>6.0f}kB  {link_per_chunk:>6.1f} M  "
                f"{p99_chunk:>9.3f}s  {p99_file:>9.3f}s  {delta:>+7.1f}%"
            )
        print()

    sweep(
        "Optimistic: each chunk gets the FULL link (distinct peers, no shared bottleneck)",
        lambda n: whole_mbps,
    )
    sweep(
        "Realistic: client downlink SHARED — each parallel chunk sees link/n Mbps",
        lambda n: whole_mbps / n,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
