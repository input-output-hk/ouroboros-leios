# Notes — table of contents

All six notes so far cover the same theme: parallel chunked downloads under
TCP CUBIC with random loss. Read them in this order; each builds on the
previous.

1. **[parallel-chunking.md](./parallel-chunking.md)** — *Foundations & math.*
   Q&A originally prompted by the question "if I split a file into n parallel
   chunks downloaded from distinct peers, is the whole-file P99 the same as
   each chunk's P99?" Establishes the max-of-iid math: file P99 sits at the
   chunk distribution's quantile at `q = 0.99^(1/n)`, which is strictly
   deeper into the chunk's right tail than chunk P99. Notes the two
   independence caveats (shared bottleneck, MC tail stability) that the
   later notes elaborate on.

2. **[parallel-chunking-results.md](./parallel-chunking-results.md)** —
   *Empirical sweep.* Runs `tools/chunk_compare.py` over the default config
   (12.5 MB / 1 Gbps / 50 ms / p=1e-4) for n ∈ {2, 4, 8, 16, 32} under both
   "optimistic" (full link per chunk) and "realistic" (link/n shared)
   bandwidth models. Five takeaways including the headline result (file P99
   drops 75% at n=32) and the floor-vs-tail framing for *why* chunking
   helps less at higher RTT.

3. **[parallel-chunking-n2-puzzle.md](./parallel-chunking-n2-puzzle.md)** —
   *Why small-n chunking underperforms.* Investigates the apparent puzzle
   that n=2 gives only ~12% P99 improvement when naive intuition suggests
   ~50%. Decomposes the gap into the max-of-two statistical penalty (file
   P99 = chunk P99.5, not chunk P99), CUBIC's size-independent loss
   recovery cost K, and the invariance of fast-path probability under
   bisection. Conclusion: chunking is a tail-management tool, not a
   throughput multiplier.

4. **[parallel-chunking-cdf-staircase.md](./parallel-chunking-cdf-staircase.md)** —
   *Why the CDF curves look like a staircase.* Each chunk download lands
   in one of a small set of discrete regimes (no-loss; loss in slow-start
   round r for each r; multi-loss). Each regime concentrates runs at a
   tight time value, producing the rise → plateau → rise pattern. Raising
   to `F_file = F_chunk^n` amplifies the steps further at large n. Lognormal
   RTT jitter blurs each step a little but doesn't change the structure.

5. **[parallel-chunking-mc-confidence.md](./parallel-chunking-mc-confidence.md)** —
   *Monte Carlo stability of tail estimates.* Quantifies how few samples
   live in the deep tail (~15 at n=32 / M=50k) and shows via 10-seed
   reruns that a CDF step at n=16 produces a ~30 % seed-to-seed range
   while bootstrap CI under-reports it by 13×. Documents the two
   diagnostics added in response (`tools/chunking_stability.py` for
   seed-to-seed CoV; `plot_chunking.py --ci` for per-n bootstrap CI
   bands) and validates at M=500k that n=16's true value sits 3% above
   the M=50k estimate.

6. **[parallel-chunking-low-p.md](./parallel-chunking-low-p.md)** —
   *The low-loss regime and the conditional metric.* At p ≲ 1e-5 the
   marginal P99 collapses to the upper tail of the no-loss slow-start
   completion (well-sampled, but uninformative about loss behavior).
   Introduces the conditional metric `P99 | ≥1 loss` — implemented as
   `tools/chunk_compare.py --conditional` — and shows that at p=1e-6 the
   conditional baseline is ~9 s vs marginal ~0.6 s, and that chunking
   still meaningfully shrinks the conditional bad-outcome magnitude
   (≈10× at n=32). Includes a sample-size caveat: the conditional metric
   needs M ≥ 500k for stable n=32 numbers.
