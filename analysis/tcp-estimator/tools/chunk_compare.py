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

With --conditional, the output adds a "P99 | ≥1 loss" companion table that
filters to runs whose timing was actually shaped by a CUBIC recovery — the
meaningful metric when p is low enough that marginal P99 just reads the
upper tail of jittered slow-start (see notes/parallel-chunking-mc-confidence.md).

Usage:
  tools/chunk_compare.py [inputs.yaml] [--conditional]
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


def _bdp_ssthresh(link_mbps: float, rtt_s: float, mss: int) -> float:
    return max(1.0, math.floor(link_mbps * 1e6 * rtt_s / 8.0 / mss))


def run_at(
    base: estimator.Config, file_kb: float, link_mbps: float, with_losses: bool = False
):
    cfg = dataclasses.replace(
        base,
        file_size_kb=file_kb,
        link_speed_mbps=link_mbps,
        initial_ssthresh_segs=_bdp_ssthresh(link_mbps, base.rtt_s, base.mss_bytes),
    )
    if with_losses:
        return estimator.monte_carlo_with_losses(cfg)
    return sorted(estimator.monte_carlo(cfg))


def conditional_chunk_p99(chunks: list[tuple[float, int]]) -> tuple[float, int, float]:
    """Return (P99|≥1 loss, count, p_loss) for a chunk-sample list of (t, n_loss)."""
    loss_times = sorted(t for t, n_loss in chunks if n_loss >= 1)
    p_loss = len(loss_times) / len(chunks) if chunks else 0.0
    if not loss_times:
        return float("nan"), 0, p_loss
    return estimator.percentile_of(loss_times, 0.99), len(loss_times), p_loss


def conditional_file_p99(
    chunks: list[tuple[float, int]], n: int, B: int, rng: random.Random
) -> tuple[float, int]:
    """Resample to estimate file P99 | at least one chunk has ≥1 loss.

    Draw B file trials of n chunks each (with replacement). For each trial,
    file time = max chunk time; loss indicator = OR over chunk loss indicators.
    Filter to file trials with ≥1 loss and report P99 of those times.
    """
    file_times_with_loss: list[float] = []
    for _ in range(B):
        draws = [chunks[rng.randrange(len(chunks))] for _ in range(n)]
        if any(c[1] >= 1 for c in draws):
            file_times_with_loss.append(max(c[0] for c in draws))
    file_times_with_loss.sort()
    if not file_times_with_loss:
        return float("nan"), 0
    return estimator.percentile_of(file_times_with_loss, 0.99), len(
        file_times_with_loss
    )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("config", nargs="?", default=str(REPO_ROOT / "inputs.yaml"))
    ap.add_argument(
        "--conditional",
        action="store_true",
        help="Also report P99|≥1 loss (chunk and file) — the meaningful "
        "metric at low p where marginal P99 just reads no-loss tail.",
    )
    ap.add_argument(
        "--file-resamples",
        type=int,
        default=200_000,
        help="Bootstrap resamples for the conditional file P99 (default: 200000)",
    )
    args = ap.parse_args()

    base = estimator.load_config(Path(args.config), None)
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

    if args.conditional:
        baseline_with_loss = run_at(base, whole_kb, whole_mbps, with_losses=True)
        p99c_chunk, n_loss, p_loss = conditional_chunk_p99(baseline_with_loss)
        print(
            f"  P[≥1 loss] = {p_loss:.4f}  ({n_loss} of {len(baseline_with_loss)} runs)"
        )
        if n_loss > 0:
            print(f"  P99 | ≥1 loss = {p99c_chunk:.3f}s")
    print()

    header = f"{'n':>3}  {'chunk':>8}  {'link/ch':>9}  {'P99_chunk':>10}  {'file_P99':>10}  {'vs base':>9}"
    cond_header = (
        f"{'n':>3}  {'chunk':>8}  {'P[chunkLoss]':>14}  {'P99|chLoss':>11}  "
        f"{'P[fileLoss]':>12}  {'file_P99|loss':>14}"
    )

    def sweep(title: str, link_for_n):
        print(title)
        print(header)
        print("-" * len(header))
        chunk_samples_for_n: dict[int, list[tuple[float, int]]] = {}
        for n in (2, 4, 8, 16, 32):
            chunk_kb = whole_kb / n
            link_per_chunk = link_for_n(n)
            if args.conditional:
                samples = run_at(base, chunk_kb, link_per_chunk, with_losses=True)
                chunk_samples_for_n[n] = samples
                sorted_chunk = sorted(t for t, _ in samples)
            else:
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

        if args.conditional and chunk_samples_for_n:
            print(f"  -- conditional on ≥1 loss event (B={args.file_resamples:,}) --")
            print(cond_header)
            print("-" * len(cond_header))
            rng = random.Random(0)
            for n in (2, 4, 8, 16, 32):
                samples = chunk_samples_for_n[n]
                p99_chunk_c, _, p_loss_chunk = conditional_chunk_p99(samples)
                p99_file_c, n_with_loss = conditional_file_p99(
                    samples, n, args.file_resamples, rng
                )
                p_loss_file = n_with_loss / args.file_resamples
                chunk_kb = whole_kb / n
                p99_chunk_str = (
                    f"{p99_chunk_c:.3f}s" if p99_chunk_c == p99_chunk_c else "n/a"
                )
                p99_file_str = (
                    f"{p99_file_c:.3f}s" if p99_file_c == p99_file_c else "n/a"
                )
                print(
                    f"{n:>3}  {chunk_kb:>6.0f}kB  {p_loss_chunk:>13.4f}  "
                    f"{p99_chunk_str:>11}  {p_loss_file:>12.4f}  {p99_file_str:>14}"
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
