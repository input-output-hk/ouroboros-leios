# Parallel chunked downloads: empirical comparison

Follow-up to [parallel-chunking.md](./parallel-chunking.md). Ran
`tools/chunk_compare.py --runs 500000` over `inputs.yaml`
(size=12500 kB, link=1000 Mbps, RTT=50 ms, p=1e-4, lognormal jitter σ=0.15).
M=500 000 was chosen for tail stability after the validation in
[parallel-chunking-mc-confidence.md](./parallel-chunking-mc-confidence.md)
showed M=50 000 single-run values for n=8 and n=16 can be seed-fragile
(the original draft of this table had n=8 at 3.465 s — 10 % above the
M=500 000 truth of 3.157 s).

## Results

```
Baseline (n=1, no chunking, full link):
  P50 = 0.526s   P95 = 1.976s   P99 = 6.717s

Optimistic: each chunk gets the FULL link (distinct peers, no shared bottleneck)
  n     chunk    link/ch   P99_chunk    file_P99    vs base
-----------------------------------------------------------
  2    6250kB  1000.0 M      3.228s      5.777s    -14.0%
  4    3125kB  1000.0 M      1.790s      5.413s    -19.4%
  8    1562kB  1000.0 M      1.007s      3.157s    -53.0%
 16     781kB  1000.0 M      0.565s      3.017s    -55.1%
 32     391kB  1000.0 M      0.358s      1.645s    -75.5%

Realistic: client downlink SHARED — each parallel chunk sees link/n Mbps
  n     chunk    link/ch   P99_chunk    file_P99    vs base
-----------------------------------------------------------
  2    6250kB   500.0 M      3.228s      5.777s    -14.0%
  4    3125kB   250.0 M      1.790s      5.413s    -19.4%
  8    1562kB   125.0 M      1.007s      3.157s    -53.0%
 16     781kB    62.5 M      0.565s      3.017s    -55.1%
 32     391kB    31.2 M      0.358s      1.645s    -75.5%
```

## Takeaways

1. **Chunking helps substantially.** File P99 drops from 6.72 s (no chunking)
   to 1.65 s with n = 32 — a 75 % reduction. The benefit comes from *tail
   shrinkage*, not from bandwidth: with smaller chunks each carries less loss
   exposure ( P[no loss in chunk] ≈ (1-p)^(packets/n) ), so each chunk's CDF
   has a much shorter right tail. Taking the max of n shorter tails still
   beats one long one — even though you're sampling at quantile `0.99^(1/n)`
   instead of 0.99. (See [parallel-chunking-n2-puzzle.md](./parallel-chunking-n2-puzzle.md)
   for why this benefit is small at n=2 and grows non-linearly with n.)

2. **"Chunk's P99" is *not* the file's P99.** Read across rows: at n = 8 the
   chunk's P99 is 1.007 s but the file's P99 is 3.157 s — confirming the math
   from the companion note: file P99 sits at the chunk's P99.87
   ( = 0.99^(1/8) ), which is much deeper into the chunk's right tail.

3. **"Optimistic" and "realistic" are identical here because the bandwidth
   cap never binds.** Steady-state CUBIC at p = 1e-4, RTT = 50 ms gives
   E[W] ≈ 111 segs (~26 Mbps) — far below either the 1000 Mbps full link or
   even 31 Mbps with n = 32 sharing. **Loss is the binding constraint, not
   bandwidth.** The realistic scenario would diverge from optimistic for
   higher p, smaller RTT, or small files where slow start drives cwnd into
   the BDP cap before encountering a loss.

4. **Chunking attacks the loss-induced tail; it can't shrink the slow-start
   ramp.** Each chunk still ramps from W₀ via doublings, so per-chunk
   wall-clock floor is roughly

   ```
   T_floor ≈ ⌈log₂(N/n / W₀)⌉ · RTT
   ```

   This is what a perfectly lossless run takes, and it scales linearly with
   RTT regardless of n. The achievable chunking gain is bounded by how much
   of P99 sits *above* T_floor — i.e., how much is killable tail. RTT sweep
   at the default config (file=12500 kB, link=1 Gbps, p=1e-4, ssthresh auto):

   | RTT     | baseline P99 | n=32 P99 | relative gain | absolute gain |
   | ------- | ------------ | -------- | ------------- | ------------- |
   | 50 ms   | 6.6 s        | 1.7 s    | **−75 %**     | 5 s           |
   | 250 ms  | 15.9 s       | 6.0 s    | **−62 %**     | 10 s          |
   | 1000 ms | 31.4 s       | 11.4 s   | **−63 %**     | 20 s          |

   At low RTT the floor is negligible (~0.5 s) and almost all of P99 is
   killable, so chunking eliminates 75 %. At high RTT the floor grows to
   ~10 s, so even perfect tail elimination caps the relative gain at
   ~65 %. The absolute saving still grows, but the *fraction* of P99 that
   chunking can attack shrinks.

5. **Quick way to map your own workloads:** drop in your `inputs.yaml` and
   rerun `tools/chunk_compare.py --runs 500000`. Configs where the slow-start
   floor dominates P99 (high RTT, small file, low loss) gain less from
   chunking relative to baseline; configs where the loss-induced tail
   dominates (heavier load, longer files, higher loss) gain more. For low p
   ( ≲ 1e-5 ) the marginal P99 reported here becomes uninformative — see
   [parallel-chunking-low-p.md](./parallel-chunking-low-p.md) for the
   conditional metric that captures chunking's benefit in that regime.
   For MC-precision considerations and seed-to-seed stability, see
   [parallel-chunking-mc-confidence.md](./parallel-chunking-mc-confidence.md).
