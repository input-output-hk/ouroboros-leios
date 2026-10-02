# Chunking at low p: marginal P99 is precise but uninformative

Companion to the parallel-chunking series:
[math](./parallel-chunking.md),
[empirical sweep](./parallel-chunking-results.md),
[n=2 puzzle](./parallel-chunking-n2-puzzle.md),
[MC confidence](./parallel-chunking-mc-confidence.md),
[CDF staircase](./parallel-chunking-cdf-staircase.md).

## Stability looks fine, but...

`tools/chunking_stability.py` at p=1e-6 over the default workload
(12.5 MB / 1 Gbps / 50 ms, 10 seeds × M=50 000):

```
  n          q   mean P99       std                  range     CoV  verdict
  1   0.990000     0.568s    0.001s [ 0.568,  0.569]s    0.1%  stable
  2   0.994987     0.521s    0.001s [ 0.519,  0.522]s    0.1%  stable
  4   0.997491     0.472s    0.001s [ 0.470,  0.473]s    0.2%  stable
  8   0.998744     0.423s    0.002s [ 0.421,  0.427]s    0.4%  stable
 16   0.999372     0.373s    0.001s [ 0.371,  0.375]s    0.4%  stable
 32   0.999686     0.321s    0.002s [ 0.318,  0.323]s    0.6%  stable
```

Every n is "stable" (CoV < 1 %). It is — but the answer is not what
you might think it is.

## What the marginal P99 is actually measuring at low p

With p=1e-6 over 8562 packets,
`P[no loss in transfer] = (1 − 1e-6)^8562 ≈ 0.9915`. So ~99.15 % of
runs are loss-free. The marginal P99 lives at quantile 0.99, which is
**inside** the no-loss region. It's reading the upper tail of jittered
slow-start completion, not loss-induced recovery.

| n | chunk pkts | P[chunk no loss] | file P99 quantile q=0.99^(1/n) | margin to no-loss frontier |
| --- | --- | --- | --- | --- |
| 1 | 8562 | 0.99147 | 0.99000 | 0.00147 inside |
| 2 | 4281 | 0.99573 | 0.99499 | 0.00074 inside |
| 8 | 1071 | 0.99893 | 0.99875 | 0.00018 inside |
| 32 | 268  | 0.99973 | 0.99969 | 0.00004 inside |

And the reported P99 values match nominal slow-start completion + ~70 ms
lognormal-jitter upper-tail offset:

| n | reported P99 | nominal no-loss time (rounds × RTT) |
| --- | --- | --- |
| 1 | 0.568 s | 10 × 50 ms = 0.500 s |
| 2 | 0.521 s | 9 × 50 ms = 0.450 s |
| 4 | 0.472 s | 8 × 50 ms = 0.400 s |
| 8 | 0.423 s | 7 × 50 ms = 0.350 s |
| 16 | 0.373 s | 6 × 50 ms = 0.300 s |
| 32 | 0.321 s | 5 × 50 ms = 0.250 s |

So the chunking "speedup" at low p is the slow-start ramp speedup
(fewer rounds when chunks are smaller). **No CUBIC recovery contributes
to marginal P99.** That's a real number but it's not what you usually
care about when asking "does chunking protect me against bad outcomes?".

## The fix: P99 | at least one loss

Add `--conditional` to `tools/chunk_compare.py` (or
`monte_carlo_with_losses` programmatically) and the picture changes
qualitatively. Each Monte Carlo trial now also reports the count of
*effective* loss events (losses that actually reshaped cwnd — losses
in the file-completing round don't count, since they don't add time),
and the conditional analysis filters to runs with ≥1 effective loss.

### Baseline (n=1) at p=1e-6

| metric | value | what it represents |
| --- | --- | --- |
| Marginal P50 | 0.505 s | typical no-loss completion |
| Marginal P99 | 0.568 s | upper tail of no-loss + jitter |
| **P[≥1 loss]** | **0.0051** | how often a loss reshapes timing |
| **P99 \| ≥1 loss** | **8.923 s** | **conditional bad-outcome magnitude** |

So at p=1e-6 the rare "bad" transfer is ~15× slower than the typical
one, but only ~1 in 200 transfers hits it. Marginal P99 hides this
entirely.

### Conditional sweep across n (p=1e-6, optimistic, M=50k initial)

(See the "Validation at M=500 000" section further below; the n=32
row in this M=50k table is based on ~10 conditional samples and is
revised upward by ~0.8 s when re-run at M=500k.)

| n | P[chunkLoss] | P99\|chunkLoss | P[fileLoss] | **file_P99\|fileLoss** |
| --- | --- | --- | --- | --- |
| 1 (baseline) | 0.0051 | 8.923 s | 0.0051 | 8.923 s |
| 2 | 0.0027 | 7.78 s | 0.0055 | **7.80 s** |
| 4 | 0.0012 | 6.77 s | 0.0050 | **6.78 s** |
| 8 | 0.0008 | 5.08 s | 0.0069 | **5.09 s** |
| 16 | 0.0006 | 3.03 s | 0.0089 | **3.04 s** |
| 32 | 0.0002 | 0.88 s | 0.0074 | **0.92 s** |

Reading: chunking **does** meaningfully attack the conditional tail
at low p — the bad-outcome magnitude drops from 8.9 s at n=1 to 0.92 s
at n=32, a ~10× reduction at M=50k. (The M=500k validation below
revises n=32 upward to 1.69 s, making the true reduction ~5×; the M=50k
~10× figure was based on only ~10 conditional samples and was
optimistic.) The probability of a bad outcome stays in the same
~0.005–0.009 band (the OR-over-chunks effect roughly cancels the
smaller per-chunk loss probability), so chunking's contribution here
is **shrinking the bad-outcome magnitude** rather than reducing its
frequency.

### Compare to p=1e-4 (current default)

| metric | value |
| --- | --- |
| Marginal baseline P99 | 6.63 s |
| Conditional baseline P99 \| ≥1 loss | 9.71 s |
| P[≥1 loss] | 0.40 |

At p=1e-4 the loss tail is already a large fraction of P99, so the
marginal and conditional metrics are close (within ~50 %) and the
existing chunk_compare table is informative on its own. At p=1e-6
they diverge by a factor of 15, and only the conditional view shows
what chunking is doing for you.

## Sample-size caveat for the conditional metric

The conditional table reports `P[chunkLoss]` for each n. Multiplying
by M (50 000) gives the count of conditional-set samples:

| n | conditional samples at p=1e-6, M=50k |
| --- | --- |
| 1 | 253 |
| 2 | 135 |
| 8 | 40 |
| 16 | 30 |
| 32 | 10 |

The n=32 row's P99|chunkLoss=0.88 s is computed from only ~10
samples — directionally suggestive, not a precise number. For
reportable conditional values at low p, bump `--runs` to 500k–1M
(the absolute number of loss-affected chunk samples is what determines
precision, and that scales linearly with M).

### Validation at M=500 000

Rerunning `chunk_compare.py /tmp/p1e-6.yaml --runs 500000 --conditional`
(1m 30s runtime — each MC trial is fast at low p since most runs are
loss-free slow-start completions):

```
Baseline (n=1):
  P[≥1 loss] = 0.0052  (2617 of 500000 runs)
  P99 | ≥1 loss = 8.904 s
```

| n | M=50k file_P99\|loss | M=500k file_P99\|loss | mean shift | conditional-set size |
| --- | --- | --- | --- | --- |
| 1 (baseline) | 8.923 s | 8.904 s | −0.019 s | 253 → 2 617 |
| 2 | 7.797 s | 7.755 s | −0.042 s | ~135 → ~1 300 |
| 4 | 6.784 s | 6.699 s | −0.085 s | ~60 → ~600 |
| 8 | 5.086 s | 5.058 s | −0.028 s | ~40 → ~400 |
| 16 | 3.044 s | 3.082 s | +0.038 s | ~30 → ~300 |
| **32** | **0.921 s** | **1.689 s** | **+0.768 s** | **~10 → ~100** |

Findings:

- **n=32 corrected substantially** — the M=50k point estimate (0.92 s)
  was based on ~10 conditional samples and was off by ~80 %; the M=500k
  value (1.69 s) is based on ~100 and is much more credible. For
  publication-grade n=32 numbers, bump further to M=2 M+ (~1 000
  conditional samples).
- **n=1–16 were already within ~1 % at M=50k** — the conditional set
  was big enough for those rows.
- **The qualitative story holds:** chunking still substantially shrinks
  the conditional bad-outcome magnitude (8.9 s → 1.7 s at n=32, ~80 %
  reduction), it's just slightly less dramatic than M=50k suggested.
- **Conditional file-loss probability is stable around 0.005** across
  all n: chunking doesn't change *how often* the bad outcome happens,
  only *how bad* it is when it does.

## Recommendation

- For p ≳ 1e-4: marginal P99 from `plot_chunking.py` and `chunk_compare.py`
  is the right thing to report. Optionally add `--conditional` for an
  extra perspective.
- For p ≲ 1e-5: marginal P99 is misleading. Always pair the report with
  the conditional table, and bump `--runs` to ensure enough loss-affected
  samples to estimate the conditional tail.
- For the very-low-p extreme (p ≤ 1e-7) where even conditional sampling
  is too sparse: move to analytical conditioning — closed-form the
  no-loss path, MC only the smaller loss-affected sub-distribution,
  combine via `E[T] = P[no loss] · E[T|no loss] + P[loss] · E[T|loss]`.
