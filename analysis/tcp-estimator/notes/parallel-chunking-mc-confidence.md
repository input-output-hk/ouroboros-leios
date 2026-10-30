# Monte Carlo confidence in chunking-plot tail estimates

Companion to [parallel-chunking.md](./parallel-chunking.md) (math),
[parallel-chunking-results.md](./parallel-chunking-results.md) (empirical
sweep), [parallel-chunking-n2-puzzle.md](./parallel-chunking-n2-puzzle.md)
(why n=2 underperforms), and
[parallel-chunking-low-p.md](./parallel-chunking-low-p.md)
(where the "precise but uninformative" trap discussed in lesson 3 below
gets a dedicated treatment plus the conditional-metric fix).
This note investigates how trustworthy the chunking plot's curves
are, especially for n ≥ 8 where we're reading quantiles deep in the
chunk distribution's tail.

## The arithmetic problem

For n parallel chunks the whole-file P99 sits at the chunk distribution's
quantile `q = 0.99^(1/n)`. With M Monte Carlo trials, only `M·(1−q)` samples
fall beyond that quantile:

| n   | q = 0.99^(1/n) | 1 − q     | tail samples at M=50k | M=500k |
| --- | -------------- | --------- | --------------------- | ------ |
| 1   | 0.9900         | 1.0 e−2   | 500                   | 5 000  |
| 2   | 0.99499        | 5.0 e−3   | 250                   | 2 500  |
| 8   | 0.99875        | 1.25 e−3  | 62                    | 625    |
| 16  | 0.99937        | 6.3 e−4   | 31                    | 312    |
| 32  | 0.99969        | 3.1 e−4   | 15                    | 156    |

At n=32 with M=50 000 we have ~15 samples in the relevant tail region. That
is not enough for stable point estimates.

The picture is worse at low p. For p=1e-6,
`P[no loss in chunk_size=8562/32] ≈ 0.99973` — i.e. the chunk's 99.97-th
percentile is right at the boundary between the fast-path (no loss) and the
rare loss-affected regime. Tiny sampling differences flip estimates between
"≈ min time" and "≈ min time + loss-recovery K".

## Verifying with bootstrap CI

Bootstrap (200 resamples) of a single M=50 000 run, default `inputs.yaml`:

```
### p = 1e-4 ###
  n  chunk kB  q for file P99   point      95% CI            CI/point
  1  12500     0.990000         6.632 s    [6.155, 6.966] s  12.2 %
  2   6250     0.994987         5.843 s    [5.769, 5.988] s   3.8 %
  8   1562     0.998744         3.465 s    [3.085, 4.997] s  55.2 %
 16    781     0.999372         3.009 s    [2.955, 3.028] s   2.5 %
 32    391     0.999686         1.656 s    [1.638, 1.676] s   2.3 %
```

The n=8 row jumps out (CI is ±55 % of the point estimate), but the n=16
row's tight CI is **misleadingly narrow** — see the seed-to-seed check
below. The chunk distribution near these quantiles has step structure
(transitions between no-loss and one-loss regimes, between one-loss and
two-loss regimes, etc.). Bootstrap resamples from the empirical sample so
it cannot see "new" rare events beyond the step.

## Seed-to-seed stability (the gold-standard check)

Re-running the same workload with 10 different RNG seeds, M=50 000 each:

```
### p = 1e-4 (10 seeds × M=50 000) ###
  n   mean P99   std       range                 CoV
  1   6.741 s    0.063 s   [6.639, 6.843] s      0.9 %
  2   5.757 s    0.023 s   [5.723, 5.794] s      0.4 %
  8   3.122 s    0.055 s   [3.080, 3.267] s      1.7 %
 16   2.919 s    0.289 s   [2.098, 3.043] s      9.9 %   ← unstable
 32   1.644 s    0.009 s   [1.631, 1.655] s      0.5 %

### p = 1e-6 ###
  n   mean P99   std       range                 CoV
  1   0.568 s    0.001 s   [0.568, 0.569] s      0.1 %
  2   0.521 s    0.001 s   [0.519, 0.522] s      0.1 %
  8   0.423 s    0.002 s   [0.421, 0.427] s      0.4 %
 16   0.373 s    0.001 s   [0.371, 0.375] s      0.4 %
 32   0.321 s    0.002 s   [0.318, 0.323] s      0.6 %
```

Three lessons:

1. **The instability is non-monotonic in n.** n=1, n=2, n=8, n=32 are
   fine; n=16 has CoV ~10 % with a 30 % range across seeds. This is a
   CDF-step hazard, not a "deeper tail = noisier" hazard. It will hit
   wherever the file-P99 quantile happens to land on a regime boundary
   for the configured n / p / file size.
2. **Bootstrap underestimates variability around CDF steps.** Bootstrap
   CI width for n=16 was 0.07 s; true seed-to-seed range was 0.94 s —
   13 × off. Bootstrap is fine for smooth regions and misleading near
   the discontinuities our chunk distributions actually have.
3. **At very low p, estimates are precise but uninformative.** All CoVs
   at p=1e-6 sit under 1 %, but only because the file-P99 essentially
   equals the no-loss minimum time. There simply isn't enough loss
   content in 50 000 trials to estimate the conditional tail.

## Validation at M=500 000

Same 10-seed test, M bumped 10×. Runtime: 8 min 10 s (linear in M).

```
### p = 1e-4 (10 seeds × M=500 000) ###
  n   mean P99   std       range                 CoV
  1   6.742 s    0.040 s   [6.669, 6.791] s      0.6 %
  2   5.771 s    0.010 s   [5.758, 5.785] s      0.2 %
  4   5.426 s    0.012 s   [5.411, 5.441] s      0.2 %
  8   3.136 s    0.018 s   [3.108, 3.164] s      0.6 %
 16   3.013 s    0.008 s   [2.998, 3.024] s      0.3 %
 32   1.642 s    0.003 s   [1.638, 1.647] s      0.2 %
```

Comparison vs M=50 000:

| n | M=50k CoV | M=500k CoV | M=50k mean | M=500k mean | mean shift |
| --- | --------- | ---------- | ---------- | ----------- | ---------- |
| 1   | 0.9 %     | 0.6 %      | 6.741 s    | 6.742 s     | +0.001 s   |
| 2   | 0.4 %     | 0.2 %      | 5.757 s    | 5.771 s     | +0.014 s   |
| 8   | 1.7 %     | 0.6 %      | 3.122 s    | 3.136 s     | +0.014 s   |
| **16** | **9.9 %** | **0.3 %** | **2.919 s** | **3.013 s** | **+0.094 s** |
| 32  | 0.5 %     | 0.2 %      | 1.644 s    | 1.642 s     | −0.002 s   |

Two findings:

- **Only n=16 was materially wrong at M=50 000.** Its CoV collapsed
  10 % → 0.3 %, the range went 0.94 s wide → 0.02 s wide, and the
  point estimate shifted +3 % (2.92 s → 3.01 s). The M=50k mean was
  biased low because the step-CDF crossing landed below the true level
  in more seeds than above. Every other n was already within ~1 % of
  the M=500k truth.

- **Total dataset error was small but localized.** The shipped
  `chunk_compare.py` table reported file_P99=3.009 s at n=16 (matches
  the M=500k truth to 0.1 %), but only because seed=42 happened to land
  on the high side of the step. Without the stability tool we wouldn't
  have known that result was seed-fragile.

## Mitigations

| Approach                              | Effort   | Variance reduction       |
| ------------------------------------- | -------- | ------------------------ |
| Bump `--runs` to 500k–1M              | trivial  | 3–10 × narrower CI       |
| Multi-seed rerun + CoV report         | small    | quantifies it            |
| Bootstrap CI band around plot curves  | small    | quantifies it visually   |
| Analytical conditioning at low p      | medium   | order-of-magnitude       |
| Importance sampling (oversample loss) | large    | 10–100 ×                 |

### Per-regime recommendation

- **p ≈ 1e-4 (current default).** M=500 000 brings every n's CoV
  under 1 % (verified, see table above). Runtime grows linearly:
  ~5 s/plot at M=50k → ~50 s at M=500k → 8 min for a full 10-seed
  stability sweep. Use M=500k when generating plots intended for
  reporting; M=50k is fine for quick iteration as long as the
  stability tool agrees.

- **p ≈ 1e-6 (realistic for well-provisioned short connections).**
  Cranking `--runs` doesn't help much for the *marginal* P99: you'd
  need ≥ ~100/p ≈ 10⁸ trials to sample the conditional loss tail
  reliably. The realistic fix is to **reframe the metric**: report
  `P99 | at least one loss` instead of marginal P99 — implemented as
  `tools/chunk_compare.py --conditional` and elaborated in
  [parallel-chunking-low-p.md](./parallel-chunking-low-p.md). For
  values still requiring extra precision after that (e.g. n=32
  conditional at very low p), bump `--runs` further so the
  conditional-set sample count grows; for the truly extreme regime
  (p ≤ 1e-7) move to analytical conditioning (closed-form the
  no-loss path, MC the smaller loss-affected sub-distribution,
  combine via the law of total probability).

### Diagnostic tooling

Both complementary checks are available in `tools/`:

- **`tools/chunking_stability.py`** — reruns the chunk sweep K times
  with different seeds, prints mean / std / range / CoV per n with a
  verdict flag (stable / ok / noisy / unstable). Run this before
  trusting a chunking plot — it's the only check that catches
  CDF-step instability like the M=50k n=16 case above.
- **`tools/plot_chunking.py --ci`** — main multi-curve plot is
  unchanged; additionally emits one per-n SVG with a pointwise
  bootstrap 95 % CI band (exact-bootstrap via `random.binomialvariate`,
  no resample-and-sort). Caveat: pointwise bootstrap *under-reports*
  uncertainty wherever the CDF has a step — at n=16 with M=50k it
  reported CI ±0.07 s, the true seed-to-seed range was ±0.94 s. The
  band shows fixed-t uncertainty cleanly; for quantile uncertainty
  (read horizontally at y=0.99) trust the stability tool instead.
