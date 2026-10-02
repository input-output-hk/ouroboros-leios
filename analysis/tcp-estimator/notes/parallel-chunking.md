# Parallel chunked downloads: does single-chunk P99 = whole-file P99?

## Question

> Can I use these plots to answer the following question? Suppose I can split
> my file into n chunks, and download each chunk independently, possibly from
> distinct peers such that slow start penalty applies to each transfer. Is the
> 99th percentile of downloading the whole file the same as the 99th
> percentile of each chunk, assuming that the downloads are parallel and each
> chunk is the same size?

## Answer

**No** — `P99(whole file) > P99(single chunk)` whenever n > 1.

### Why

Parallel ⇒ total time = max(T₁, …, Tₙ). For n i.i.d. chunks with CDF F,

  P(max ≤ t) = F(t)ⁿ ⇒ the file's q-quantile is at F⁻¹(q^(1/n))

For q = 0.99:

| n   | quantile of chunk dist you must look up |                              |
| --- | --------------------------------------- | ---------------------------- |
| 1   | 0.990                                   | no chunking — sanity check   |
| 2   | 0.9950                                  | chunk's P99.5  = file's P99  |
| 4   | 0.9975                                  | chunk's P99.75 = file's P99  |
| 10  | 0.9990                                  | chunk's P99.9  = file's P99  |
| 100 | 0.9999                                  | chunk's P99.99 = file's P99  |

So you're always sampling further into the chunk's right tail than 0.99, and
the answer climbs (slowly) with n.

### Using these plots correctly for parallel chunking

You no longer need to compute `q^(1/n)` by hand — three tools in `tools/`
do the chunking analysis end-to-end:

- **`tools/chunk_compare.py [--runs 500000]`** — tabular sweep of file P99
  vs n at the configured workload, in both "optimistic" (each chunk gets
  the full link) and "realistic" (chunks share a single link/n) bandwidth
  models. Add `--conditional` to also report `P99 | ≥1 loss`, the
  meaningful metric at low p.
- **`tools/plot_chunking.py [--runs 500000] [--ci]`** — overlay SVG plot
  of the implied whole-file CDF for each n on one axes; the leftward shift
  and tail collapse make chunking's benefit visible at a glance. `--ci`
  additionally writes a per-n companion plot with a bootstrap 95 % CI band.
- **`tools/chunking_stability.py`** — reseed sanity check. Reruns the
  chunk-distribution sim K times with different RNG seeds and reports
  CoV per n; flags rows that are seed-fragile so you don't mistake a
  lucky M=50 k sample for a stable answer.

### Three caveats glossed over by the question

- **"Independent" assumes losses on different paths are uncorrelated.**
  Chunks pulled to the same client share your access link and receive queue;
  if that's the bottleneck, they're not independent (and effective per-chunk
  bandwidth becomes link/n).
- **MC tail stability.** The marginal P99 at chunking-relevant quantiles
  lives on only `M·(1-q)` samples, so M=1 000 gives ~10 tail samples and
  is unreliable. See [parallel-chunking-mc-confidence.md](./parallel-chunking-mc-confidence.md);
  the empirical recommendation is **M=500 000** at p ~ 1e-4 for reportable
  numbers, and `tools/chunking_stability.py` catches the residual
  seed-fragile rows.
- **Marginal P99 degenerates at low p.** When p ≲ 1e-5 most runs are
  loss-free and the marginal P99 just reads the upper tail of jittered
  slow-start completion. The conditional metric `P99 | ≥1 loss` is the
  right thing to look at; see
  [parallel-chunking-low-p.md](./parallel-chunking-low-p.md).

### Does chunking actually help?

Whether parallel chunking *lowers* the file's P99 vs. a single one-shot
download depends on the parameters: smaller chunks each carry less loss
exposure (so each chunk's CDF is tighter), but you're sampling deeper into
the n-fold worst case. The empirical answer for the default config and
its RTT sensitivity is in
[parallel-chunking-results.md](./parallel-chunking-results.md); the
mechanism explanation (chunking attacks the loss tail, not the slow-start
floor) is in
[parallel-chunking-n2-puzzle.md](./parallel-chunking-n2-puzzle.md).
