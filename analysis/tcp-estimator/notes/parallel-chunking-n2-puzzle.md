# Why does n=2 give only a 12 % P99 improvement, not 2×?

Companion to [parallel-chunking.md](./parallel-chunking.md) (math) and
[parallel-chunking-results.md](./parallel-chunking-results.md) (empirical sweep).

## Observation

In the chunking-overlay plot for the default config (12.5 MB, 1 Gbps,
50 ms, p=1e-4), the n=1 and n=2 CDF curves sit very close together.
Naively one would expect downloading half the file in parallel to take
roughly half the time. Instead, file P99 only drops from 6.60 s to 5.79 s
(–12 %).

The n=2 chunk's *own* P99 is 3.24 s — roughly half the full-file P99, so the
naive intuition is correct *at the chunk level*. The discrepancy comes from
two separate effects compounding.

## 1. The max-of-two penalty

For n=2 parallel i.i.d. chunks, file time = max(T₁, T₂). Under independence:

  file_P99 = chunk's quantile at 0.99^(1/2) = chunk_P99.5

So the file's P99 is *not* the chunk's P99 — it's drawn from deeper in the
chunk's right tail. With 100 000 MC trials:

| chunk percentile | time |
| ---------------- | -------------- |
| P99              | 3.24 s         |
| **P99.5**        | **5.79 s** ← becomes file P99 |
| P99.9            | 8.30 s         |

That 0.5 % step nearly doubles the time because the chunk distribution is
heavy-tailed.

## 2. Why the chunk's tail is heavy

A CUBIC loss event has wall-clock recovery cost ≈ K = ∛(W_max·β/C). When the
loss hits at high cwnd (late slow start, W_max ≈ 1280 for half-file), K ≈ 10 s.
**That recovery cost does not scale with chunk size** — only with W_max. Half-file
just sees fewer bad-loss events, not cheaper bad-loss events. Each additional
0.5 % into the tail samples a worse-cwnd loss or a multi-loss run.

## 3. The fast-path mass is invariant under bisection

The really structural insight: the probability of taking the lossless fast path
doesn't improve with n=2. For the default config, the file's total packet
count is

  N_total = ⌈ file_size_bytes / MSS ⌉ = ⌈ 12 500 000 / 1460 ⌉ = **8562 packets**

and each half carries N_total / 2 = 4281 packets. Under Bernoulli p=1e-4 per
packet:

```
P[whole file lossless]    = (1-p)^N_total            = (1-1e-4)^8562 ≈ 0.425
P[both halves lossless]   = ((1-p)^(N_total/2))^2    = (1-p)^N_total ≈ 0.425
```

n=2 doubles each chunk's individual lossless probability (0.65 vs 0.42), but
the max-of-two re-multiplies the failure exposure back to baseline. So the
**42.5 % fast-path mass doesn't shift** — only the conditional-on-loss tail
shape changes (modestly, because bad-loss K is unchanged).

## 4. Why larger n breaks out of this

At n=16 the chunk is 781 kB ≈ 535 packets:

- **P[no loss in chunk] ≈ (1-p)^535 ≈ 0.948** — almost every chunk takes the
  fast path. (1-p)^(N/n) → 1 as n grows much faster than the max-of-n
  re-multiplication can drag it back.
- **Conditional bad losses have a smaller W_max** — cwnd never has time to
  ramp into the high hundreds before the chunk completes, so the worst K is
  much smaller too.

Both effects compound, and that's why the overlay plot shows curves crowding
together for small n then fanning out dramatically for n ≥ 8.

## Generalization

Chunking is a **tail-management tool, not a throughput multiplier**. For the
median or mean, n=2 yields only a ~1.1× speedup for the same reason: the
fast-path mass is invariant. Chunking pays off when the chunk size drops low
enough that each chunk's individual loss-induced tail collapses — at which
point the max-of-n penalty is also light because the chunk distribution is
nearly degenerate at its minimum time.
