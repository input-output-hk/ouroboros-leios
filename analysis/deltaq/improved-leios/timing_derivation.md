# Derivation of Per-Transaction Apply and Reapply Timing Constants

This document explains how the `applyTx` and `reapplyTx` per-transaction timing
constants used in the ΔQ model were derived, why the original Haskell constants
were incorrect, and what the corrected values are.

---

## 1. Data Source

All timing measurements come from `post-cip/empirical-distributions/block-edf.csv`,
produced by running `db-analyser` on Cardano mainnet.  The CSV has 9 381 rows, one
per unique (Tx count, Block size) bin, with the following columns:

| Column | Description |
|--------|-------------|
| `Tx count` | Number of transactions in the block |
| `Block size [kB]` | Block body size in kilobytes |
| `Apply [ms]` | Total wall-clock time to call `applyBlock` on this block |
| `Reapply [ms]` | Total wall-clock time to call `reapplyBlock` |
| `Fraction of blocks [%/100]` | Fraction of mainnet blocks in this bin |

**Critical note:** `Apply [ms]` and `Reapply [ms]` are **per-block totals**, not
per-transaction costs.  A block with 300 transactions has one row; its `Apply [ms]`
is the time to apply all 300 transactions together.

The dataset covers blocks with 0 to 385 transactions.  Empty blocks (n = 0) occupy
18 rows and represent 5.8% of all blocks by frequency.  The analysis below uses
only the 9 363 non-empty rows unless noted.

---

## 2. The Original Haskell Constants

`analysis/deltaq/linear-leios/src/DeltaQ/Leios/EmpiricalDistributions.hs`
defines the timing distributions as:

```haskell
applyTxs   = scaleMixtureDQ 100  0.01059939845  0.02548883812  -- 10.60 ms, 25.49 ms
reapplyTxs = scaleMixtureDQ 2500 0.002711165479 0.02441685076  --  2.71 ms, 24.42 ms
```

The comment points to `block-edf.csv` as the source.  To verify the derivation,
compute the **unweighted arithmetic mean and standard deviation of all rows**
of the `Apply [ms]` and `Reapply [ms]` columns (including n = 0 rows):

```python
mean(Apply [ms]  for all rows) = 10.5994 ms ≈ 10.60 ms  ✓
std (Apply [ms]  for all rows) = 25.4888 ms ≈ 25.49 ms  ✓
mean(Reapply [ms] for all rows) = 2.7112 ms ≈  2.71 ms  ✓
std (Reapply [ms] for all rows) = 24.4169 ms ≈ 24.42 ms ✓
```

The match is exact to five significant figures, confirming this is the derivation.

### Why this is wrong

The constants are per-block means used as per-tx costs.  There are two distinct
methodological errors:

**Error 1 — wrong unit.**  `Apply [ms]` records the time to apply an entire block.
Using its mean as a per-tx cost implicitly assumes every block contains exactly one
transaction.  In practice the mean block has 15 transactions (frequency-weighted),
so the per-tx cost is overstated by roughly that factor in expectation.

**Error 2 — unweighted over bins.**  The CSV has one row per unique bin, not one
row per block occurrence.  The `Fraction of blocks` column records how common each
bin is.  Taking an unweighted mean treats a rare Plutus-heavy bin — say, a 1-tx
block taking 1 328 ms to apply — identically to a common simple-payment bin
representing millions of blocks.  The unweighted mean is not a frequency-weighted
average; it is strongly influenced by rare outliers.

Combined, these errors overstate the per-tx apply cost by approximately **20×**
and the per-tx reapply cost by approximately **40×**.

---

## 3. Estimation Approaches Considered

We evaluated five approaches to deriving a per-tx timing estimate.  All use the
non-empty-block rows (n > 0) of `block-edf.csv`.

### 3.1 Unweighted mean of Apply[ms] / n

The simplest correction: divide each block's total time by its transaction count,
then take the unweighted mean.

$$\hat\mu_\text{A} = \frac{1}{R}\sum_{b} \frac{\text{Apply}_b}{n_b}$$

where $R$ is the number of non-empty rows.

| Estimate | Apply (ms/tx) | Reapply (ms/tx) |
|----------|--------------|-----------------|
| Mean     | 1.139        | 0.356           |
| Std dev  | 6.660        | 6.507           |

**Problem:** Still treats every bin equally, regardless of frequency.  Rare
Plutus-heavy 1-transaction bins (Apply/n up to 999 ms/tx) inflate the mean
substantially.  The large σ (6.66 ms/tx ≫ μ 1.14 ms/tx) indicates extreme
right skew.

### 3.2 Block-frequency-weighted mean of Apply[ms] / n

Weight each bin by its `Fraction of blocks`:

$$\hat\mu_\text{B} = \frac{\sum_b f_b \cdot \dfrac{\text{Apply}_b}{n_b}}{\sum_b f_b}$$

| Estimate | Apply (ms/tx) | Reapply (ms/tx) |
|----------|--------------|-----------------|
| Mean     | 0.605        | 0.092           |
| Std dev  | 0.931        | 0.717           |

This weights each mainnet **block occurrence** equally.  The σ is still large
relative to μ, reflecting the mix of cheap simple-payment blocks and expensive
Plutus blocks.

### 3.3 Transaction-weighted mean of Apply[ms] / n

Weight each bin by the number of transactions it contributes to the mainnet
transaction stream, i.e.\ by $n_b \times f_b$:

$$\hat\mu_\text{C} = \frac{\sum_b f_b \cdot \text{Apply}_b}{\sum_b n_b \cdot f_b}
= \frac{E_f[\text{Apply}]}{E_f[n]}$$

This answers the question: *"What is the expected apply cost for a randomly
chosen transaction in the mainnet transaction stream?"*

The variance formula is:

$$\hat\sigma^2_\text{C} = \frac{\sum_b f_b \cdot \text{Apply}^2_b / n_b}{\sum_b n_b \cdot f_b} - \hat\mu^2_\text{C}$$

(Each transaction in bin $b$ has cost Apply$_b$ / $n_b$; the second moment
is computed accordingly.)

| Estimate | Apply (ms/tx) | Reapply (ms/tx) |
|----------|--------------|-----------------|
| **Mean** | **0.507**    | **0.070**        |
| **Std dev** | **0.527** | **0.265**        |

The σ/μ ratio for apply is ≈ 1.04, reflecting the realistic mix of cheap and
expensive transactions in the mainnet stream.

### 3.4 WLS linear regression: Apply[ms] ~ n

Fit Apply[ms] = α + β·n using frequency weights:

$$(\hat\alpha, \hat\beta) = \arg\min_{\alpha,\beta}
\sum_b f_b \left(\text{Apply}_b - \alpha - \beta n_b\right)^2$$

| Coefficient | Apply | Reapply |
|-------------|-------|---------|
| Intercept α (ms) | 2.100 | 0.233 |
| Slope β (ms/tx)  | 0.368 | 0.055 |

$\hat\beta$ estimates the **marginal** per-tx cost, with the per-block overhead
$\hat\alpha$ separated out.  For large $n$, the overhead is negligible and
β dominates.

**Problem:** The regression overpredicts apply time for large blocks by 3–5×
(see §4 sanity checks), indicating the linear model is a poor fit outside
the 1–20 tx range that dominates the data by block frequency.

### 3.5 Multivariate regression from ReadMe

`post-cip/apply-reapply/ReadMe.md` reports a multivariate regression on a richer
dataset with block size (bytes), Tx count, number of transaction inputs, and
Plutus steps as regressors.  The per-tx coefficients:

| Regression | Apply per tx | Reapply per tx |
|------------|-------------|----------------|
| Linear model (mean) | 0.160 ms/tx | 0.035 ms/tx |
| 75th-percentile      | 0.220 ms/tx | 0.042 ms/tx |

These isolate the per-tx contribution while controlling for other block
characteristics.  The per-tx regression coefficient is lower than the
transaction-weighted mean because it separates out block-size effects.

---

## 4. Sanity Checks

To assess data fit quality, we compare the predicted total apply time for
buckets of blocks grouped by transaction count against the observed mean:

| Block size | Blocks (% of mainnet) | Txs (% of mainnet) | Obs. Apply mean | Obs. Apply/n | Tx-wt pred (§3.3) |
|-----------|----------------------|---------------------|----------------|-------------|-------------------|
| 1–5 tx   | 28.7 %               | 5.4 %               | 8.79 ms        | 3.43 ms/tx  | 1.62 ms           |
| 6–20 tx  | 44.7 %               | 35.1 %              | 9.75 ms        | 0.92 ms/tx  | 6.03 ms           |
| 21–50 tx | 24.3 %               | 49.7 %              | 10.42 ms       | 0.36 ms/tx  | 15.90 ms          |
| 51–100 tx | 2.3 %               | 9.3 %               | 13.68 ms       | 0.20 ms/tx  | 35.25 ms          |
| 101–200 tx | < 0.1 %            | 0.4 %               | 19.63 ms       | 0.15 ms/tx  | 69.54 ms          |
| 201–385 tx | < 0.1 %            | 0.1 %               | 27.46 ms       | 0.11 ms/tx  | 124.71 ms         |

**Key observation:** The per-tx cost decreases with block size, from 3.43 ms/tx
for 1–5 tx blocks down to 0.11 ms/tx for 200–385 tx blocks.  No simple constant
model fits all bucket sizes simultaneously.

The tx-weighted mean (0.507 ms/tx) overestimates the large-block regime (201–385
tx: 0.11 ms/tx) by a factor of 4–5×.  This occurs because the transaction-weighted
mean is pulled toward the small-block regime (1–20 tx: 73% of txs by count), where
occasional Plutus-heavy transactions inflate per-tx cost.

For blocks with 50+ transactions — the closest in-sample analogue to large EB
closures — a linear fit gives slope = 0.083 ms/tx (Apply) and 0.030 ms/tx
(Reapply), with R² = 0.22 and 0.05 respectively (low, because even within this
range there is variance from Plutus outliers).

**Why does per-tx cost decrease with n?**  Several contributing factors:

1. *Fixed per-block overhead.* The ledger evaluates block-level validity checks
   (header validation, script context setup, ledger rule preconditions) once per
   block, independent of transaction count.  Larger blocks amortize this overhead
   over more transactions.

2. *Selection effect.*  Large blocks on mainnet tend to contain simple payment
   transactions (which are cheap), while Plutus-heavy transactions are rare and
   tend to appear in smaller blocks, often filling the block's execution-unit budget
   alone.

---

## 5. Recommended Values and Rationale

The constants adopted in `analysis.py` are from **approach 3.3** (transaction-weighted
mean):

| Constant | Value | Source |
|----------|-------|---------|
| `APPLY_MU_S`    | 0.507 ms/tx | tx-weighted mean of Apply[ms]/n |
| `APPLY_SIGMA_S` | 0.527 ms/tx | tx-weighted std dev              |
| `REAPPLY_MU_S`  | 0.070 ms/tx | tx-weighted mean of Reapply[ms]/n |
| `REAPPLY_SIGMA_S` | 0.265 ms/tx | tx-weighted std dev            |

**Rationale:**

- *Correct unit.*  Apply[ms]/n is a per-tx quantity; taking its tx-weighted mean
  gives E[cost per tx] directly.
- *Correct weighting.*  Each transaction in the mainnet stream contributes equally,
  rather than each bin or each block.
- *Includes Plutus.*  Plutus transactions contribute to the average at their actual
  mainnet rate; no separate Plutus-step model is required.
- *Conservative.*  As shown in §4, the tx-weighted mean (0.507 ms/tx) overestimates
  the per-tx cost for large blocks (0.11 ms/tx at n ≥ 200).  For EB closures of
  thousands of transactions, the true per-tx cost is likely *lower* than 0.507 ms/tx.
  Using the higher value is therefore a safe-sided choice for feasibility analysis.

**Comparison of estimates:**

| Approach | μ_apply (ms/tx) | μ_reapply (ms/tx) | μ_eff (ms/tx) | 1-core cliff |
|----------|-----------------|-------------------|---------------|-------------|
| Original Haskell (wrong) | 10.60 | 2.71 | 4.03 | ≈ 1.5 MB |
| Unweighted mean of Apply/n (§3.1) | 1.14 | 0.36 | 0.49 | ≈ 11 MB |
| Block-freq-weighted mean (§3.2) | 0.61 | 0.09 | 0.18 | ≈ 30 MB |
| **TX-weighted mean (§3.3, adopted)** | **0.507** | **0.070** | **0.143** | **≈ 38 MB** |
| WLS slope (§3.4) | 0.368 | 0.055 | 0.107 | ≈ 50 MB |
| ReadMe regression mean (§3.5) | 0.160 | 0.035 | 0.056 | ≈ 96 MB |
| Large-block OLS slope (n ≥ 50) | 0.083 | 0.030 | 0.039 | ≈ 138 MB |

The analytic single-core ceiling is:
$S^\text{max} \approx (7\,\text{s} - 1.5\,\text{s}_\text{network}) / \mu_\text{eff} \times 1\,\text{kB/tx}$.

**Every estimate except the original Haskell constants** places the quorum cliff
well above the 12 MB CIP-0164 target.  Under any of these corrections, CPU is
not the binding constraint.

---

## 6. Caveats and Extrapolation Concerns

**1. Data range is 0–385 transactions per block.**
EB closures in the CIP target range contain 1 000–12 000 transactions (at 1 kB/tx).
All estimates extrapolate outside the observed range by a factor of 3–30×.  There
is no guarantee the per-tx cost remains constant at the same level.

**2. Per-tx cost decreases with block size.**
The data clearly show that larger blocks have lower per-tx apply costs (§4).  The
tx-weighted mean is pulled toward small blocks (which dominate by count) and likely
*overstates* the per-tx cost for large EB closures.  In this sense the adopted
value is conservative (safe-sided).

**3. Plutus fraction may differ.**
The tx-weighted mean includes Plutus transactions at their mainnet rate (roughly
5–10% by tx count in recent epochs).  If the EB closure composition differs — for
example, if an adversary deliberately fills closures with Plutus-heavy transactions —
the per-tx cost could be substantially higher.  The original Haskell constants
(10.60 ms/tx) can be interpreted as a worst-case dominated by a single Plutus
transaction in a 1-tx block.

**4. Measurement machine is unknown.**
`db-analyser` was run on one machine; the timing constants are specific to that
machine's CPU, cache hierarchy, and garbage-collection behaviour.  Validator nodes
running on different hardware will see different values.

**5. reapplyTx skips script execution; applyTx does not.**
In the EB closure validation model, cache-hit transactions use `reapplyTx`
(scripts already validated, cached) and cache-miss transactions use `applyTx`
(full validation including scripts).  The σ for `reapplyTx` (0.265 ms/tx) is
lower than for `applyTx` (0.527 ms/tx), consistent with this: when scripts are
skipped, variance is mainly from UTXO lookup and ledger-state serialisation,
both of which are more predictable than Plutus execution.

---

## 7. Effect on the DeltaQ Model

With the corrected constants, the effective per-tx cost for the mixed
apply/reapply model is:

$$\mu_\text{eff} = \pi_1 \mu_\text{apply} + \pi_2 \mu_\text{reapply}
= \tfrac{1}{6}(0.507) + \tfrac{5}{6}(0.070) = 0.143\,\text{ms/tx}$$

$$\sigma^2_\text{eff} = \pi_1(\sigma^2_\text{apply} + (\mu_\text{apply} - \mu_\text{eff})^2)
                     + \pi_2(\sigma^2_\text{reapply} + (\mu_\text{reapply} - \mu_\text{eff})^2)
\approx (0.363\,\text{ms/tx})^2$$

For $N = 12\,288$ transactions (12 MB closure at 1 kB/tx), the CPU-only
validation time is approximately:

$$T_\text{CPU} \sim \mathcal{N}(1\,759\,\text{ms},\;40\,\text{ms})$$

The 99th percentile (≈ 1 852 ms) is well under the 7 000 ms voter deadline,
so **on the CPU axis alone, $P_\text{validating} \approx 1$ at all closure
sizes up to 12 MB on a single core**.  The single-core CPU ceiling is
approximately $S^\text{max}_\text{CPU} \approx 5.5\,\text{s} / 0.143\,\text{ms/tx}
\times 1\,\text{kB/tx} \approx 38$ MB.

**The CPU contribution is not the binding constraint.**  Under the TCP CUBIC
network model (`analysis.py` §NETWORK MODEL), the full voter pipeline includes:

1. EB body fetch over blended multi-hop paths (up to 512 kB in the generic
   sweep), which alone has a fat tail — about 11% of voters fail this step
   even at zero closure.
2. 1-hop fetch of the missing closure fraction $\pi_1 \cdot S_{EB\text{-}tx}$
   over a randomly chosen distance category.  At 12 MB the missing fraction
   is 2 MB; over a 268 ms OWD long-haul link this takes ≈ 8.85 s, exceeding
   the 7 s deadline.
3. CPU reapplication (as derived in this document).

The resulting full $P_\text{validating}$ from the model is therefore:

| $S_{EB-tx}$ | $P_\text{validating}$ | Notes |
|-------------|-----------------------|-------|
| 0 MB        | 0.891                 | EB-body multi-hop fetch only |
| 4 MB        | 0.865                 | + 683 kB missing-closure 1-hop |
| 8 MB        | 0.812                 | + 1.33 MB missing-closure 1-hop |
| 12 MB       | **0.747**             | + 2.00 MB missing-closure (8.85 s on long links) |

At 12 MB the value 0.747 is just below the 0.75 quorum threshold, collapsing
$P_\text{quorum}$ to 0.440 and $P_\text{cert}$ to 0.218.  The
**Praos interruption probability** ($P_\text{interrupted} \approx 0.503$) caps
$P_\text{cert}$ at $\approx 0.497$ whenever $P_\text{quorum} \approx 1$ (i.e.
for $S_{EB-tx} \leq 8$ MB); at 12 MB the additional network-driven quorum
collapse pulls $P_\text{cert}$ further below that cap.

The per-tx timing constants derived in this document are therefore correct and
unaffected by the network discussion — they govern the CPU step only, which is
not the binding constraint at any tested size.

---

## 8. Reproducing the Numbers

```python
import csv, statistics, math

rows = []
with open('post-cip/empirical-distributions/block-edf.csv') as f:
    for row in csv.DictReader(f):
        rows.append({
            'n':       int(row['Tx count']),
            'apply':   float(row['Apply [ms]']),
            'reapply': float(row['Reapply [ms]']),
            'frac':    float(row['Fraction of blocks [%/100]']),
        })

nz = [r for r in rows if r['n'] > 0]

# Transaction-weighted mean: weight each bin by n_txs × fraction
tw = sum(r['n'] * r['frac'] for r in nz)
mu_apply   = sum(r['frac'] * r['apply']   for r in nz) / tw  # 0.5072 ms/tx
mu_reapply = sum(r['frac'] * r['reapply'] for r in nz) / tw  # 0.0703 ms/tx

# Transaction-weighted variance: E[X^2] - E[X]^2, X = time_b / n_b
e2_apply   = sum(r['frac'] * r['apply']**2   / r['n'] for r in nz) / tw
e2_reapply = sum(r['frac'] * r['reapply']**2 / r['n'] for r in nz) / tw
sigma_apply   = math.sqrt(e2_apply   - mu_apply**2)   # 0.5268 ms/tx
sigma_reapply = math.sqrt(e2_reapply - mu_reapply**2)  # 0.2648 ms/tx
```

All derivations are also available in the analysis script
`analysis/deltaq/improved-leios/analysis.py` and documented in `analysis_log.md`
(Log 013).
