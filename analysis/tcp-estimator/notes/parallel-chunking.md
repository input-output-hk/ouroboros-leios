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

1. Re-run with `file_size_kb` set to your **chunk size** (S/n), not the
   whole-file size — slow start applies per transfer, so the chunk's CDF,
   not the whole-file CDF, is what you need.
2. Read off the **q^(1/n)** quantile of that chunk CDF; that's the file's
   `P_q` under parallel chunking. The current plot only marks the requested
   percentile and P99 — for chunked analysis you'd want to read a different
   percentile off the curve (or pass `-p` set to `0.99^(1/n)` to drop the
   marker exactly where you need it).

### Two caveats glossed over by the question

- **"Independent" assumes losses on different paths are uncorrelated.**
  Chunks pulled to the same client share your access link and receive queue;
  if that's the bottleneck, they're not independent (and effective per-chunk
  bandwidth becomes link/n).
- **MC tail stability.** 1000 MC runs gives ~10 samples in the top 1 %. For
  stable readings at `0.99^(1/n)` when n is moderate, bump
  `monte_carlo_runs` to 10 000+.

### Does chunking actually help?

Whether parallel chunking *lowers* the file's P99 vs. a single one-shot
download depends on the parameters: smaller chunks each carry less loss
exposure (so each chunk's CDF is tighter), but you're sampling deeper into
the n-fold worst case. The simulator can answer this empirically by
running both configurations and comparing.
