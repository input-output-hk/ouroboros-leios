# Why do the chunking plot CDFs look like a staircase?

Companion to the parallel-chunking series:
[math](./parallel-chunking.md),
[empirical sweep](./parallel-chunking-results.md),
[n=2 puzzle](./parallel-chunking-n2-puzzle.md),
[MC confidence](./parallel-chunking-mc-confidence.md),
[low-p regime](./parallel-chunking-low-p.md).

## Observation

The whole-file CDF curves in `chunking.svg` and its per-n companions
visibly rise → plateau → rise → plateau, not as a smooth S-curve. The
effect is more pronounced for larger n. It's not a rendering artifact;
it's a real property of the discrete-time CUBIC simulation.

## Cause: discrete loss-round outcomes

Every chunk download lands in one of a small set of regimes, and each
regime concentrates runs at a tight time value:

1. **No-loss completion** — all packets delivered without retransmit.
   Time = (slow-start rounds to complete) × RTT. For the default
   12.5 MB / 1 Gbps / 50 ms config that's ~10 rounds × 50 ms ≈ 0.5 s.
   This is the biggest mode (~42 % of full-file runs at p=1e-4).

2. **One loss in round r.** The trajectory is:
   - r rounds of slow start before the loss → r · RTT seconds
   - cwnd ← W_max · (1−β); W_max ← cwnd_at_loss
   - CUBIC concave recovery, K = ∛(W_max · β / C) seconds to climb
     back to W_max
   - Remaining packets delivered as cwnd recovers

   Slow-start W_max values are themselves a discrete set
   `{W_0, 2 W_0, 4 W_0, …}`, so each (loss-round, W_max) pair produces
   a tight cluster of completion times.

3. **Two or more losses.** Rarer, even more discrete; populates further
   steps in the right tail.

## Why F_file = F_chunk^n sharpens it

Raising to a power *flattens flat regions and steepens steep regions*.
A part of F_chunk that goes from 0.998 → 0.999 (slope ~1) becomes a
part of F_file = F_chunk^32 that goes from 0.94 → 0.97 (slope ~3). So
**at large n the staircase becomes visually more pronounced**, not less.

## Why the steps aren't perfectly vertical

Two smoothing mechanisms blur the otherwise-perfect step structure:

- **Lognormal RTT jitter** (σ=0.15 in the default config) spreads each
  round's wall-clock duration. A cluster that would sit on a single t
  value gets a Gaussian-ish spread of width ~σ · T_round.
- **Multi-loss interactions.** Within a recovery trajectory another
  loss can hit, shifting the completion time. Rare at p=1e-4 but
  contributes some smoothing.

## Identifying specific steps in the n=1 curve (default config)

| feature on plot | regime                       | approximate fraction |
| --------------- | ---------------------------- | -------------------- |
| Step near 0.5 s | no loss                      | ~42 %                |
| Step near 0.7–1 s | loss in round 9 (or late 8) | ~30 % combined       |
| Step near 1.5 s | loss in round 7              | ~6 %                 |
| Step near 3 s   | loss in round 6              | ~3 %                 |
| Step near 4–5 s | loss in round 5              | ~1.5 %               |
| Step near 6–7 s | loss in round 4              | ~0.5 % (= the P99)   |

Earlier loss → larger W_max-relative recovery → longer remaining-bytes
delivery at a depressed cwnd → step further to the right.

## Bottom line

The staircase is the honest output of a discrete-time CUBIC simulation
with deterministic recovery dynamics: there really is a small finite
set of outcome modes, and the CDF reflects that. If a smoother curve
were preferred for presentation, the options are:

- **More RTT jitter** — less realistic.
- **Kernel density smoothing on the empirical CDF** — cosmetic, doesn't
  change the underlying physics.
- **Higher loss rate** — more multi-loss runs blur the structure
  naturally, but obviously changes the workload.

In every case the underlying model would still encode the same step
structure; presentation choices just hide it.
