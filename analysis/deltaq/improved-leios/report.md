# Improved ΔQ Model for Linear Leios EB Diffusion

## Table of Contents

- [1. Executive Summary](#executive-summary)
- [2. Protocol Recap](#protocol-recap)
- [3. Bugs Fixed in the Prior Analysis](#bugs-fixed-in-the-prior-analysis)
    - [3.1 RB path structure](#rb-path-structure)
    - [3.2 EB closure size](#eb-closure-size)
    - [3.3 Scale mixture vs. fixed-N distribution for reapplication](#scale-mixture)
- [4. Model Description](#model-description)
    - [4.1 Numerical Backend](#numerical-backend)
    - [4.2 Network Model](#network-model)
    - [4.3 Transaction Timings](#transaction-timings)
    - [4.4 Voter Validation Outcome (certRB Path)](#voter-validation-outcome-certrb-path)
    - [4.5 Certification Probability](#certification-probability)
        - [4.5.1 P_validating](#p-validating)
        - [4.5.2 P_quorum](#p-quorum)
        - [4.5.3 P_interrupted](#p-interrupted)
- [5. Results](#results)
    - [5.1 Sweep over S_EB-tx](#sweep)
        - [5.1a Mathis (Reno/AIMD, conservative)](#sweep-mathis)
        - [5.1b CUBIC (RFC 8312, modern Linux default)](#sweep-cubic)
    - [5.2 Network Diffusion of the EB Closure](#network-diffusion-of-the-eb-closure)
    - [5.3 Sensitivity: 1-hop vs Multi-hop EB Closure Fetch](#sensitivity-1-hop-vs-multi-hop-eb-closure-fetch-voter-path)
        - [Full-blended worst case](#full-blended-worst-case-catastrophic-pre-diffusion-failure)
        - [Maximum feasible closure when 1-hop fails](#max-feasible)
    - [5.4 Network Model Sensitivity (Mathis vs CUBIC vs loss rate)](#network-model-sensitivity-mathis-vs-cubic-vs-loss-rate)
        - [Caveats common to both models](#caveats-common-to-both-models)
    - [5.5 TxCache Miss Rate Sensitivity (π₁ sweep)](#pi1-sensitivity)
- [6. Comparison with Prior Analysis](#comparison-with-prior-analysis)
- [7. Limitations and Assumptions](#limitations-and-assumptions)
- [8. Recommendations](#recommendations)
- [9. Plot Guide](#plot-guide)
- [10. Artifact Index](#artifact-index)
- [11. References](#references)

---

## 1. Executive Summary

This report presents a corrected and extended ΔQ analysis of Endorser Block (EB)
diffusion in Linear Leios. It fixes three structural bugs in the previous
analysis, introduces a proper numerical (discretized CDF) backend, re-derives
the per-transaction timing constants from the empirical `block-edf.csv` dataset,
and instantiates the model under **two TCP congestion-control models** —
**Reno** (via the Mathis equation) and **CUBIC** — to bound the
network-induced sensitivity.

*Why TCP congestion control matters here.*  Cardano peer-to-peer diffusion of
blocks, EBs, and EB-closure transactions runs over long-lived TCP connections
between SPO nodes.  Effective throughput on each connection is determined not
by raw link capacity but by the **TCP congestion-control algorithm** running
in the sender's kernel.  Reno (RFC 5681, the legacy AIMD reference) and CUBIC
(RFC 8312, the modern Linux default since 2.6.19) respond differently to
packet loss: their steady-state throughput scales as $p^{-1/2}$ (Reno/Mathis)
vs $p^{-3/4}$ (CUBIC), giving CUBIC ~11× more throughput at $p = 10^{-4}$.
Because EB diffusion deadlines are tight (7 s for voters, 14 s for the full
round), the choice of throughput model could in principle determine whether
a 12 MB closure certifies or fails the quorum threshold — so we evaluate
both and report whether the gap matters in the empirically-supported
operating regime.

**Key findings (corrected per-tx timing, both network models, $p = 10^{-4}$,
prior-model default $\pi_1 = 1/6$, RTTs taken from the original Praos paper's
Table 1; see §5.5 for the empirical $\pi_1 \approx 0.06$ update):**

CPU is not the binding constraint at any closure size ≤ 12 MB.  Single-core
voter CPU completes in $< 2$ s for the 12 MB case ($\mu_\text{eff} = 0.143$
ms/tx).  The **1-hop missing-closure fetch** is the dominant network step,
and it completes well within the 7 s voter deadline at every CIP-target size
under either throughput model:

| $S_{EB-tx}$ | $P_\text{cert}$ (Mathis) | $P_\text{cert}$ (CUBIC) | Δ      |
|-------------|--------------------------|-------------------------|--------|
| 1 MB        | **0.497**                | **0.497**               | —      |
| 4 MB        | **0.497**                | **0.497**               | —      |
| 8 MB        | **0.497**                | **0.497**               | —      |
| **12 MB**   | **0.497**                | **0.497**               | —      |

Under **Mathis** ($T \propto p^{-1/2}$, the conservative Reno/AIMD model), the
2 MB missing-closure fetch at 12 MB takes ≈ 4.4 s over long-haul (134 ms OWD →
268 ms RTT) links — comfortably within the 7 s voter deadline.
$P_\text{validating} = 0.948$, $P_\text{quorum} \approx 1.000$, and
$P_\text{cert}$ stays at the Praos cap of ≈ 0.497.

Under **CUBIC** ($T \propto p^{-3/4}$, RFC 8312), the same fetch completes in
≈ 2.0 s.  $P_\text{validating} = 0.992$, $P_\text{quorum} \approx 1.000$, and
$P_\text{cert}$ is also at ≈ 0.497.

**Bottom line.** Under the 1-hop approximation and the Praos paper's RTT
values, **the 12 MB CIP target is robustly feasible under both throughput
models** — the Mathis-vs-CUBIC distinction is immaterial at every tested
size.  The 1-hop assumption itself is the remaining load-bearing input;
see §5.3 and `plots/network_model_comparison.svg`.

**TxCache miss rate $\pi_1$.**  The prior Haskell model fixed
$\pi_1 = 1/6 \approx 0.167$ via a hand-chosen Markov chain.  Extracting
$\pi_1$ empirically from the `post-cip/mempool-measurements` dataset (three
AWS regions during the BAU window) gives:

- Cross-region mean: **$\pi_1 \approx 0.06$**
- Cross-region worst-pair: $\pi_1 \approx 0.085$
- Empirical range: $\pi_1 \in [0.02,\,0.09]$

The prior value is ~3× the empirical mean.  See `pi1_derivation.md` for the
derivation.  **Both Mathis and CUBIC give $P_\text{cert} \approx 0.497$ at
every closure size up to 12 MB across the entire empirical $\pi_1$ range,
and the conclusion is unchanged at $\pi_1 = 1/6$.**  Sensitivity to $\pi_1$
appears only in the extreme tail (Mathis fails at $\pi_1 = 0.50$, 12 MB;
CUBIC remains feasible across the full sweep).  See §5.5 and
`plots/pi1_sensitivity.svg`.

The certification probability is capped at ≈ **50%** by the Praos leader
schedule whenever quorum is met — a fundamental property of the protocol,
independent of the throughput model.

The **1-hop approximation is the remaining load-bearing assumption**: it
holds only when transactions have already pre-diffused via tx-submission.
Without pre-diffusion the full closure must traverse the blended multi-hop
network, with two distinct failure modes at 12 MB:

- *Mathis* delivers within 14 s only 13.9% of the time, and the 7 s voter
  deadline plus 75% quorum threshold collapse $P_\text{cert}$ to ≈ 0.
- *CUBIC* delivers within 14 s ≈ 99% of the time, but only 31% of voters
  complete the full pipeline in 7 s, so quorum still fails and
  $P_\text{cert}$ is again ≈ 0.

See §5.3's "Full-blended worst case" subsection for the full derivation.
Operationally the effective $P_\text{cert}$ is $\alpha \cdot
P_\text{cert,1-hop}$ where $\alpha$ is the probability that pre-diffusion
is operating normally — at $\alpha \to 1$ the 1-hop result is correct, and
the full-blended scenario only becomes relevant during catastrophic
protocol failure (an out-of-scope question for this report).

---

## 2. Protocol Recap

Linear Leios extends Ouroboros Praos by adding Endorser Blocks (EBs). The
relevant timing pipeline (one round) is:

```
  slot:  |---L_hdr---|---L_hdr---|---L_vote---|---L_diff---|---L_hdr---|
             (1) RB    (2) EB      voting wdw   EB diffuse    (3) RB
             header    header                   + cert        header
             diffuses  diffuses                 diffuses      (next rnd)
  total: 3×L_hdr + L_vote + L_diff = 3+4+7 = 14 slots
```

(Linear Leios has no Input Blocks; those belong to Full Leios.)  The three
$L_\text{hdr}$ periods correspond to the three header-diffusion steps in
the round: the current RB header, the EB header, and the certifying RB
header at the end of the round.

An EB is certified when ≥ τ·m = 75% × 600 = 450 committee members vote for it
within the voting window (7 slots from round start). If certified, the next
ranking block (RB) carries the EB certificate rather than transactions.

**RB structure (critical):** An RB contains *either* an EB certificate (certRB)
*or* transactions (txRB), never both simultaneously. The prior analysis forced
both paths in parallel — this is incorrect.

---

## 3. Bugs Fixed in the Prior Analysis

### 3.1 RB path structure

Original code (`DeltaQ/Leios.hs`, line 128):
```haskell
processRBandEB = processRB ./\. processEB   -- WRONG: forces both paths
```
Fixed: use a probabilistic choice weighted by $P_{certified}$:
```
cdf_validate_rb(p_cert) = p_cert × certRB_path + (1-p_cert) × txRB_path
```

### 3.2 EB closure size

The original model had no parametric EB closure size. The block size used for
diffusion was a fixed uniform choice {1, 64, 256, 512} kB, and the reapply
distribution used a hardcoded N=2500 transactions.

Fixed: the EB closure is parameterised by $S_{EB-tx}$, the total closure size,
and `reapply_txs_cdf(s_eb_tx_kb)` derives the correct number of transactions:

$$N_{txs} = \min\left(\lfloor S_{EB-tx} / \overline{t_x} \rfloor,\; 16000\right)$$

where $\overline{t_x}$ = 1 kB (average transaction size) and 16 000 is the
maximum number of transaction references a 512 kB EB body can hold.

### 3.3 Scale mixture vs. fixed-N distribution for reapplication {#scale-mixture}

The original model used a *scale mixture* for the reapply CDF:

$$F_\text{mix}(t) = \frac{1}{N}\sum_{k=1}^{N} \Phi\!\left(\frac{t - k\mu}{\sqrt{k}\,\sigma}\right)$$

This models a block of *random* size $k \sim \mathcal{U}(1, N)$ – appropriate
for the Praos `applyTxs` path where the block size is unknown, but **wrong** for
EB closure validation where the validator must process *all* $N$ transactions.

Fixed: use the CLT approximation for the *fixed-N* case:

$$F_\text{fixed}(t) = \Phi\!\left(\frac{t - N\mu}{\sqrt{N}\,\sigma}\right)$$

This is significantly more pessimistic for large $N$:

| $S_{EB-tx}$ | $N_{txs}$ | Mix model mean | Fixed-N mean (correct) |
|-------------|-----------|----------------|------------------------|
| 1 MB        | 1 024     | 73 ms          | 147 ms                 |
| 2 MB        | 2 048     | 147 ms         | 293 ms                 |
| 4 MB        | 4 096     | 293 ms         | 587 ms                 |
| 12 MB       | 12 288    | 879 ms         | 1.76 s                 |

The scale mixture underestimates the mean by exactly 2×: under $k \sim
\mathcal{U}(1, N)$ the expected work is $E[k]\mu = (N/2)\mu$ versus $N\mu$
for the fixed-N case.  With the corrected per-tx constants
($\mu_\text{eff} = 0.143$ ms/tx), the Fixed-N times are well under the
7-second voter deadline for all sizes shown, so the 2× factor no longer
changes the feasibility conclusion — but the fixed-N model is still the
correct one to use.

**Clarification on what is and is not random across validators.**
A natural question: if a validator already has all closure transactions in
its mempool, does it have less work to do — and does that make the number
of transactions processed a random variable, justifying the scale mixture?

The answer is no, for two reasons:

1. *All N transactions must be processed regardless of mempool state.*
   Even a transaction the validator has seen before must be re-checked against
   the *current* ledger state via `reapplyTx`.  Ledger state at certification
   time may differ from when the transaction first arrived.  A correct
   implementation cannot skip transactions it happens to have cached.

2. *The scale mixture models the wrong quantity as random.*
   `scaleMixtureDQ N` treats the *count* of transactions as $k \sim
   \mathcal{U}(1, N)$, implying the validator randomly skips a fraction of
   the closure.  The actual source of variability across validators is the
   *cost per transaction*, not the number of transactions: a cache hit pays
   $\mu_\text{reapply}$ while a cache miss pays $\mu_\text{apply}$.  This
   per-transaction randomness is captured correctly by the effective mean
   $\mu_\text{eff} = \pi_1 \mu_\text{apply} + \pi_2 \mu_\text{reapply}$
   (Section 4.4), with N fixed.

The number of transactions *fetched* over the network does vary across
validators (approximately $\pi_1 N$ on average), but this affects only the
network fetch step, which is modelled separately in
`cdf_fetch_missing_eb_closure`.

---

## 4. Model Description

### 4.1 Numerical Backend

Rather than the piecewise-polynomial backend (which suffers from exponential
blowup under sequential composition), we use a **discretized CDF** backend:

- Grid: $N = 4000$ points, $\Delta t = 10$ ms, $T_\text{max} = 40$ s
- Sequential composition: FFT-based convolution — $O(N \log N)$
- All other operators (last-to-finish, first-to-finish, choice): pointwise

This is equivalent in design to the `Discretized` Haskell module proposed in
the `deltaq/mw/approx` branch and the `Sampled` backend in `deltaq/rationals`.
The 10 ms resolution is sufficient for this analysis (timing differences relevant
to the protocol are on the order of 100 ms or larger).

### 4.2 Network Model

The path-length distribution (multi-hop diffusion) is taken from `DeltaQ.Praos`,
based on the empirical path-length distribution of a regular random graph
(2500 nodes, degree 10):

| Path length | Probability (%) |
|-------------|-----------------|
| 1           | 0.40            |
| 2           | 3.91            |
| 3           | 31.06           |
| 4           | 61.85           |
| 5           | 2.78            |

**Single-hop transfer time** is modelled using **TCP slow start** with a
selectable steady-state congestion-control model.  Common parameters:

| Parameter     | Value      |
|---------------|-----------|
| MSS           | 1460 B    |
| Initial cwnd  | 10 MSS    |
| Loss rate $p$ | $10^{-4}$ |
| Link cap      | 1 Gbit/s  |
| OWD short     | 6 ms (RTT 12 ms)   |
| OWD medium    | 34.5 ms (RTT 69 ms) |
| OWD long      | 134 ms (RTT 268 ms) |

The OWDs are derived from Table 1 of the original Praos report
(`docs/deltaq_PraosModel.pdf` §3), which gives **round-trip times** of
12 / 69 / 268 ms for short / medium / long distances between blockchain
nodes; we halve these to obtain one-way delays.

The congestion window grows exponentially each RTT during slow start and is
capped at a model-specific steady-state window $W_\text{ss}$:

| Model    | Steady-state window $W_\text{ss}$                                          | $W_\text{ss}$ at $p = 10^{-4}$ |
|----------|----------------------------------------------------------------------------|--------------------------------|
| Mathis   | $\text{MSS}/\sqrt{p}$  (Reno/AIMD; Mathis et al. 1997)                     | 146 000 B  (= 100 MSS ≈ 146 kB)   |
| CUBIC    | $\text{MSS} \cdot \big(\tfrac{C(4-\beta)}{4\beta}\big)^{1/4} \cdot p^{-3/4}$ (Ha, Rhee & Xu 2008; RFC 8312, with $C=0.4$, $\beta=0.3$) | 1 538 590 B  (≈ 1.54 MB)          |

*Units note.* Throughout this report kB = 1000 B and MB = 10⁶ B (decimal,
SI-style — consistent with networking conventions).  The exception is the
§5.4 caveat table where the byte-by-byte cwnd progression is more readable
in kiB = 1024 B; that section labels its rounded values as "kiB" explicitly.

*RTT convention.* The OWDs above are derived from the Praos paper's RTT
values (Table 1 of PraosModel.pdf), halved.  Our model then computes
RTT = 2 · OWD internally — so the effective RTTs used here match the
Praos paper exactly.

The two models differ in how steady-state throughput responds to loss:
$T_\text{Mathis} \propto p^{-1/2}$ (steep falloff), $T_\text{CUBIC} \propto p^{-3/4}$
(shallower falloff, hence more throughput at low $p$).  Mathis is the
conservative AIMD bound; CUBIC matches the Linux kernel default for low-loss
high-BDP paths.  See §5.4 for the loss-rate sensitivity comparison and
`plots/network_model_comparison.svg`.

Each hop's distance category (short/medium/long) is drawn with equal probability
(1/3 each).  The EB body uses the blended multi-hop delay (up to 512 kB, uniform
choice over {1, 64, 256, 512} kB).  The **missing EB closure** uses a single hop
from the forwarding peer (per README recommendation: first-order approximation).

### 4.3 Transaction Timings

From `post-cip/empirical-distributions/block-edf.csv` (mainnet measurements),
using **transaction-weighted** per-tx statistics:

| Operation  | $\mu$ (ms/tx) | $\sigma$ (ms/tx) | Use |
|------------|---------------|-------------------|-----|
| `applyTx`  | 0.507         | 0.527             | txRB path; also cache-miss txs in EB closure |
| `reapplyTx`| 0.070         | 0.265             | cache-hit txs in EB closure |

`reapplyTx` is cheap because script execution results are cached from the first
`applyTx`.  A voter can only use `reapplyTx` for a transaction it has already
validated (a TxCache hit); freshly fetched cache-miss transactions require the
full `applyTx`.

**See `timing_derivation.md` for the full derivation:** the source dataset,
the five candidate estimators we considered, the rationale for adopting the
tx-weighted mean, sanity checks against per-bucket observations, caveats
about extrapolating outside the 0–385 tx/block empirical range, and
reproducing Python code.

**Note on the original Haskell constants.** The prior Haskell ΔQ model
(`linear-leios/src/DeltaQ/Leios/EmpiricalDistributions.hs`) used
$\mu_\text{apply} = 10.60$ ms/tx and $\mu_\text{reapply} = 2.71$ ms/tx,
derived as the **unweighted arithmetic mean of the `Apply[ms]` and
`Reapply[ms]` columns** of `block-edf.csv`.  Two methodological problems
affect those constants:

1. *Per-block, not per-tx.*  The `Apply[ms]` column records the total time to
   apply *all* transactions in a block, not the per-transaction cost.  Taking
   the unweighted mean of a per-block quantity yields the mean block apply time
   ($\approx 10.6$ ms/block), not a per-tx figure.

2. *Unweighted over bins.*  `block-edf.csv` has one row per unique (tx-count,
   block-size) bin.  The unweighted mean weights each bin equally, regardless
   of the `Fraction of blocks` column.  Rare Plutus-heavy bins (e.g., a block
   with 21 transactions taking 1 328 ms) receive the same weight as common
   simple-payment bins that represent much of the block history.

The corrected values weight each transaction equally:
$\mu = \frac{\sum_b f_b \cdot \text{time}_b}{\sum_b f_b \cdot n_b}$,
where $f_b$ is the fraction of blocks in bin $b$ and $n_b$ is the transaction
count.  This gives the expected per-tx cost for a randomly chosen transaction
from the mainnet distribution, including Plutus costs at their actual frequency.
The original constants overstated the per-tx cost by approximately 20× (apply)
and 40× (reapply).

### 4.4 Voter Validation Outcome (certRB Path)

```
VOTER PIPELINE:
  EB body arrival (blended delay, 1–512 kB)
  →  Fetch missing closure txs (1-hop, π₁ · S_EB_tx)
  →  applyTx   for π₁·N_txs cache-miss transactions  [expensive]
     reapplyTx for π₂·N_txs cache-hit  transactions  [cheap]
     (all N_txs processed sequentially on one core; multi-core
      parallelism is out of scope for this report)

  Total must complete within 7 slots (voter deadline)
```

The effective per-transaction CPU cost is a weighted mixture (worked here
at the prior-model $\pi_1 = 1/6$ for continuity; the empirical mean
$\pi_1 \approx 0.06$ from §5.5 would slightly reduce $\mu_\text{eff}$):

$$\mu_\text{eff} = \pi_1 \mu_\text{apply} + \pi_2 \mu_\text{reapply}
= \tfrac{1}{6}(0.507) + \tfrac{5}{6}(0.070) = 0.143\,\text{ms/tx}$$

The full mixture variance (Law of Total Variance, including between-component
term) gives:

$$\sigma^2_\text{eff} = \pi_1(\sigma^2_\text{apply} + (\mu_\text{apply} - \mu_\text{eff})^2)
                     + \pi_2(\sigma^2_\text{reapply} + (\mu_\text{reapply} - \mu_\text{eff})^2)
\approx (0.363\,\text{ms})^2$$

For $N = 12{,}288$ transactions (12 MB closure at 1 kB/tx, the CIP-0164
target) the CPU validation time is approximately

$$T_\text{CPU} \sim \mathcal{N}\!\left(N\mu_\text{eff},\; N\sigma^2_\text{eff}\right)
= \mathcal{N}\!\left(1{,}757\,\text{ms},\;(40\,\text{ms})^2\right)$$

with 99th percentile ≈ 1.85 s (Normal CLT).

*Caveat on $\sigma$.*  The values $\sigma_\text{apply} = 0.527$ and
$\sigma_\text{reapply} = 0.265$ ms/tx are tx-weighted standard deviations
of `Apply[ms]/n` taken from `block-edf.csv` bin means (which record per-bin
*means*, not individual tx times).  They therefore capture only
*between-bin* spread of per-tx mean costs; *within-bin* per-tx variance
(most notably Plutus-heavy outlier transactions) is unmeasured and not
reflected here.  As a sensitivity check, substituting the more
conservative frequency-weighted *block-level* $\sigma$ from
`timing_derivation.md` §3.2 ($\sigma_\text{apply} \approx 0.93$,
$\sigma_\text{reapply} \approx 0.72$ ms/tx) inflates $\sigma_\text{eff}$
to 0.77 ms/tx and gives a 99th percentile of ≈ 1.96 s.  Pushing $\sigma$
further (e.g., to the §3.1 unweighted block-level $\sigma \approx 6.66$
ms/tx) raises the 99th percentile to ≈ 3.1 s.  All three estimates stay
well under the 7-second voter deadline, so **CPU is non-binding at the
CIP target on a single core under any plausible $\sigma$**; the
single-core ceiling is ≈ 38 MB.

The above isolates the CPU step.  The full voter pipeline adds EB-body
diffusion and missing-closure fetch on top; these network steps keep
$P_\text{validating}$ above the 0.75 quorum threshold at every CIP-target
size under both throughput models, so $P_\text{cert}$ stays at the Praos
cap (§5.1).  See `timing_derivation.md` §7 for the CPU-only derivation.

### 4.5 Certification Probability

$$P_\text{cert} = P_\text{quorum} \times (1 - P_\text{interrupted})$$

It is assembled from three independent sub-probabilities.

#### 4.5.1 $P_\text{validating}$ {#p-validating}

Run the full voter pipeline CDF through the 7-second voter deadline
($3 L_\text{hdr} + L_\text{vote} = 7$ slots):

```
fetch EB body  →  fetch missing closure txs (1-hop)  →  reapply all N_txs
```

$P_\text{validating} = P(\text{pipeline completes} \leq 7\,\text{s})$.
For example, at the CIP-0164 target $S_{EB-tx} = 12$ MB (12 288 txs at
1 kB/tx) under the generic EB-body sweep, the per-step contributions are:

- **EB body fetch** — blended multi-hop transfer of an EB body uniformly
  drawn from $\{1, 64, 256, 512\}$ kB; mean ≈ 1 s.  The tail is driven by
  the 512 kB upper bound traversing the modal 3–4-hop long-haul paths
  (see the path-length distribution in §4.2).
- **Missing-closure fetch (1-hop)** — single-hop transfer of
  $\pi_1 \cdot S = 2$ MB for cache-miss voters; ≈ 4.4 s under Mathis and
  ≈ 2.0 s under CUBIC.
- **CPU reapply** — mean $N \mu_\text{eff} = 12{,}288 \times 0.143$ ms
  $\approx 1.76$ s, with 99th percentile ≈ 1.85 s.

The combined pipeline gives $P_\text{validating} \approx 0.948$ under
Mathis and $\approx 0.992$ under CUBIC at 12 MB — both well above the
0.75 quorum threshold.  $P_\text{validating}$ falls only slightly with
closure size (see §5.1), so the quorum threshold is met with substantial
margin under both throughput models for every $S_{EB-tx} \leq 12$ MB.

#### 4.5.2 $P_\text{quorum}$ {#p-quorum}

Each of 2500 SPOs is independently elected to the 600-member committee via
Poisson sortition: SPO $i$ with relative stake $s_i$ is elected with probability
$1 - e^{-\tilde{m} s_i}$, where $\tilde{m}$ is calibrated so that the expected
committee size equals 600.  If elected, an SPO casts a successful vote with
probability $P_\text{validating}$, so its individual success probability is:

$$p_i = P_\text{validating} \times (1 - e^{-\tilde{m} s_i})$$

The total vote count $V = \sum_i X_i$ (with $X_i \sim \text{Bernoulli}(p_i)$) is
approximated by a Normal distribution via the CLT:

$$V \sim \mathcal{N}(\mu_V,\, \sigma^2_V), \quad
  \mu_V = \sum_i p_i, \quad \sigma^2_V = \sum_i p_i(1-p_i)$$

$$P_\text{quorum} = P(V \geq \tau m) \approx 1 - \Phi\!\left(\frac{\tau m - \mu_V}{\sigma_V}\right)$$

This is where the **sharp quorum cliff** originates.  When $P_\text{validating}$
falls below the quorum fraction $\tau = 0.75$, the expected vote count
$\mu_V = P_\text{validating} \times 600$ drops below the threshold $\tau m = 450$.
Because $\sigma_V \approx 10$–12 votes, being even $\approx 20$–50 votes short
is a multi-$\sigma$ event and $P_\text{quorum}$ collapses rapidly.  In the
present results $P_\text{validating}$ stays at or above 0.948, so $\mu_V \geq
569$ and the margin to the 450 threshold is ≈ 120 votes (≈ 11 σ) — the
cliff exists in the model but is nowhere near triggered at any CIP-target
size under either throughput model.

Under the **Mathis** network model, $P_\text{validating}$ is ≈ 1.000 at
small closure sizes and declines to 0.948 at $S_{EB-tx} = 12$ MB.
$\mu_V = 0.948 \times 600 = 569$ expected votes — well above the 450
threshold — so $P_\text{quorum} \approx 1.000$ across the entire sweep.

Under **CUBIC**, the same fetches complete faster: $P_\text{validating}$
is ≈ 1.000 at small sizes and 0.992 at 12 MB.  $\mu_V = 0.992 \times 600
= 595$ — essentially at the upper limit — so $P_\text{quorum} \approx
1.000$.

In both models $P_\text{cert}$ stays at the Praos cap of $\approx 0.497$
for every CIP-target closure size; see §5.1 for the full per-model tables.

#### 4.5.3 $P_\text{interrupted}$ {#p-interrupted}

Regardless of voting success, a Praos block produced during the 14-slot window
can build on the chain before all nodes have received the EB, violating the
security guarantee ("during $L_\text{diff}$ no new RB is added, giving nodes
time to apply the EB").  The waiting time to the next Praos block is
Exponential($f = 1/20$), so:

$$P_\text{interrupted} = 1 - e^{-f L} = 1 - e^{-14/20} \approx 0.503$$

This is a pure consequence of the Praos slot schedule.  It cannot be improved
by tuning $S_{EB-tx}$, and it caps $P_\text{cert}$ at $\approx 0.497$ whenever
$P_\text{quorum} \approx 1$ — which is the case at every closure size up to
12 MB under both throughput models.  The formula is taken from the prior
analysis report (Section 5.2.2).

---

## 5. Results

### 5.1 Sweep over $S_{EB-tx}$ (single-core reapplication, both network models) {#sweep}

The same per-tx timing constants are used for both runs; only the steady-state
TCP window differs.  Results are side-by-side for direct comparison.

*Column note.* $P_\text{valid}$ uses the 7 s voter deadline
($3 L_\text{hdr} + L_\text{vote}$) — this is the *liveness* constraint
for casting a vote within the voting window.  $P(\text{certRB} \leq 14s)$
uses the 14 s round duration ($L_\text{total}$) — this is the *safety*
constraint that every node finishes processing the certifying RB before
the next round, and is paired with $P_\text{interrupted}$ (§4.5.3), which
also uses $L = 14$ s.  The two deadlines measure different things; the
7 s constraint is already absorbed in $P_\text{valid}$ (and through it in
$P_\text{cert}$), so it does not appear again as a separate column.

#### 5.1a Mathis (Reno/AIMD, conservative) {#sweep-mathis}

| $S_{EB-tx}$ | $P_\text{valid}$ | $P_\text{quorum}$ | $P_\text{cert}$ | P(certRB ≤ 14s) | P(cert × safe) |
|-------------|------------------|-------------------|-----------------|-----------------|----------------|
| 0 MB        | 0.9996           | 1.0000            | 0.4966          | 1.0000          | **0.497** ✓    |
| 1.0 MB      | 0.9978           | 1.0000            | 0.4966          | 1.0000          | **0.497** ✓    |
| 2.0 MB      | 0.9973           | 1.0000            | 0.4966          | 1.0000          | **0.497** ✓    |
| 4.0 MB      | 0.9965           | 1.0000            | 0.4966          | 1.0000          | **0.497** ✓    |
| 8.0 MB      | 0.9862           | 1.0000            | 0.4966          | 0.9999          | **0.497** ✓    |
| **12.0 MB** | **0.9482**       | **1.0000**        | **0.4966**      | **0.9993**      | **0.496** ✓    |

The two effects that constrain $P_\text{validating}$ — EB-body multi-hop
fetch and missing-closure single-hop fetch — both fit comfortably within
the 7 s voter deadline.  The 2 MB long-haul missing-fetch at 12 MB takes
≈ 4.4 s under Mathis (vs the 7 s deadline), leaving margin for the EB
body fetch and CPU reapply.  $P_\text{validating}$ drops only
slightly with $S_{EB-tx}$ — from ≈ 1.000 at 0 MB to 0.948 at 12 MB — and stays
well above the 0.75 quorum threshold at every tested size.  The
$\mu_V = 0.948 \times 600 = 569$ expected votes at 12 MB is a $> 11\sigma$
margin above the 450-vote threshold; $P_\text{quorum}$ rounds to 1.000.

Plots: `plots/mathis/`.

#### 5.1b CUBIC (RFC 8312, modern Linux default) {#sweep-cubic}

| $S_{EB-tx}$ | $P_\text{valid}$ | $P_\text{quorum}$ | $P_\text{cert}$ | P(certRB ≤ 14s) | P(cert × safe) |
|-------------|------------------|-------------------|-----------------|-----------------|----------------|
| 0 MB        | 1.0000           | 1.0000            | 0.4966          | 1.0000          | **0.497** ✓    |
| 1.0 MB      | 0.9999           | 1.0000            | 0.4966          | 1.0000          | **0.497** ✓    |
| 2.0 MB      | 0.9998           | 1.0000            | 0.4966          | 1.0000          | **0.497** ✓    |
| 4.0 MB      | 0.9998           | 1.0000            | 0.4966          | 1.0000          | **0.497** ✓    |
| 8.0 MB      | 0.9966           | 1.0000            | 0.4966          | 1.0000          | **0.497** ✓    |
| **12.0 MB** | **0.9924**       | **1.0000**        | **0.4966**      | **1.0000**      | **0.497** ✓    |

The CUBIC steady-state window is ~10× larger than Mathis's at $p = 10^{-4}$,
so each transfer completes ~2× faster than under Mathis once slow start ends.
At 12 MB, $P_\text{validating} = 0.992$ and $P_\text{quorum} \approx 1.000$.

Plots: `plots/cubic/`.

The **Praos interruption probability** ($\approx 0.503$) fixes the ceiling
on $P_\text{cert}$ at $\approx 0.497$ whenever quorum is met — which is the
case at every tested size under either model.  **There is no quorum cliff
in the 0–12 MB range under either model.**

### 5.2 Network Diffusion of the EB Closure

With CPU no longer the binding constraint, network diffusion is the primary
bottleneck.  Two scenarios are distinguished — both reported under each model.

**1-hop approximation** (voter path in §5.1): each cache-miss node fetches only
the missing fraction ($\pi_1 \cdot S_{EB-tx} \approx S_{EB-tx}/6$) from its
upstream peer over a single hop.

| $S_{EB-tx}$ | Missing ($\pi_1 \cdot S$) | $P_\text{valid}$ Mathis | $P_\text{valid}$ CUBIC |
|-------------|--------------------------|-------------------------|------------------------|
| 1.0 MB      | 171 kB                   | 0.998                   | 1.000                  |
| 4.0 MB      | 683 kB                   | 0.996                   | 1.000                  |
| 8.0 MB      | 1.33 MB                  | 0.986                   | 0.997                  |
| 12.0 MB     | 2.0 MB                   | **0.948**               | **0.992**              |

Both models stay well above the 0.75 quorum threshold across the full range,
so $P_\text{quorum} \approx 1$ and $P_\text{cert}$ stays at the Praos cap.

**Full blended diffusion** (worst case — transactions not pre-diffused; the
entire $S_{EB-tx}$ must traverse the blended multi-hop network):

| $S_{EB-tx}$ | P(full diffusion ≤ 14s) Mathis | P(full diffusion ≤ 14s) CUBIC |
|-------------|--------------------------------|-------------------------------|
| 1.0 MB      | 1.000                          | 1.000                         |
| 2.0 MB      | 0.957                          | 1.000                         |
| 4.0 MB      | 0.615                          | 1.000                         |
| 8.0 MB      | 0.230                          | 1.000                         |
| 12.0 MB     | **0.139**                      | **0.991**                     |

The two columns bracket the realistic operating regime.  Under Mathis the
worst-case scenario at 12 MB is still poor (network delivers within 14 s only
14% of the time); under CUBIC the network is essentially never the limiting
factor (99% deliver within 14 s).  Either way, the 1-hop approximation is
**load-bearing** for the main results: it is only justified if the raw
transactions referenced by the EB body have already diffused via
tx-submission *before* the EB is produced.  In Linear Leios (which has no
Input Blocks — transactions diffuse solely via the tx-submission
miniprotocol) this typically holds under normal operation, but is not
guaranteed under adversarial conditions or heavy mempool load.  The full P_cert under the full-blended worst case is derived in §5.3
("Full-blended worst case") and is ≈ 0 under both models (the bottleneck
shifts from network delivery to the tighter 7 s voter deadline and the 75%
quorum threshold).

See `plots/mathis/network_diffusion.svg` and `plots/cubic/network_diffusion.svg`
for the per-model CDFs.

### 5.3 Sensitivity: 1-hop vs Multi-hop EB Closure Fetch (voter path)

For every CIP-target size up to 12 MB, the 1-hop and blended-missing
multi-hop models both give $P_\text{cert}$ at the Praos cap ≈ 0.497 under
either throughput model — the missing-closure fetch ($\pi_1 \cdot S$, up to
2 MB at 12 MB for $\pi_1 = 1/6$) is small enough to complete in time even
over multi-hop paths.  At 12 MB, **with $\pi_1 = 1/6$** (the conservative
prior-Haskell default; §5.5 sweeps $\pi_1$ explicitly, and the empirical
mean $\pi_1 \approx 0.06$ would shrink the missing fraction to 0.72 MB
and push both rows higher):

| Scenario | Mathis $P_\text{valid}$ | Mathis $P_\text{cert}$ | CUBIC $P_\text{valid}$ | CUBIC $P_\text{cert}$ |
|----------|:-:|:-:|:-:|:-:|
| 1-hop missing (default) | 0.948 | 0.497 | 0.992 | 0.497 |
| Blended-missing | 0.854 | 0.497 | 0.942 | 0.497 |

The blended-missing case lowers $P_\text{validating}$ by ~10 percentage
points under both models, but both stay well above the 0.75 quorum threshold,
so $P_\text{cert}$ is unchanged — the Praos cap continues to bind, not
quorum.  The 1-hop vs blended-missing distinction is therefore *not* what
determines feasibility in the realistic-RTT regime; it would only matter
near $\pi_1 \cdot S \approx W_\text{ss}$ or with substantially longer RTTs.

Plots: `plots/mathis/sensitivity_1hop_vs_blended.svg`,
       `plots/cubic/sensitivity_1hop_vs_blended.svg`.

#### Full-blended worst case (catastrophic pre-diffusion failure)

The two scenarios above (1-hop and blended of the *missing fraction*
$\pi_1 \cdot S$) both assume that the voter is missing only a small fraction
of the closure — they reflect normal mempool-fragmentation dynamics.  A
strictly worse scenario is **total pre-diffusion failure**: tx-submission
hasn't worked at all, every voter is missing the *entire* closure, and the
full $S_{EB-tx}$ must traverse the blended multi-hop network.  At
$S_{EB-tx} = 12$ MB:

| Quantity | Mathis (full-blended) | CUBIC (full-blended) |
|----------|:-:|:-:|
| Network-only $P(\text{12 MB} \leq 7\text{s})$  | 2.6%   | 64.8% |
| Network-only $P(\text{12 MB} \leq 14\text{s})$ | 13.9%  | 99.1% |
| $P_\text{validating}$ (voter pipeline ≤ 7 s)   | 0.017  | 0.306 |
| $P_\text{quorum}$                              | ≈ 0    | ≈ 0   |
| $P_\text{cert}$                                | ≈ 0    | ≈ 0   |

CUBIC's 99% "delivers within 14 s" is misleading on its own — it doesn't
carry over to P_cert, for two compounding reasons:

1. **Voter deadline is 7 s, not 14 s.**  Only 65% of CUBIC blended
   12 MB transfers finish within 7 s (median ≈ 5.5 s), and the full
   voter pipeline (which adds EB body fetch and CPU on top) pushes
   $P_\text{validating}$ down to 0.31.
2. **The 75% quorum threshold dwarfs $P_\text{validating}$.**  With
   $\mu_V = 0.306 \times 600 \approx 184$ expected votes vs the 450-vote
   threshold, $P_\text{quorum}$ collapses to ≈ 0 even under CUBIC.

**Combining the two regimes.**  Realistic operation is a mixture, not a
strict either/or:

$$P_\text{cert,effective} = \alpha \cdot P_\text{cert,1-hop} + (1-\alpha) \cdot P_\text{cert,full-blended}
\approx \alpha \cdot P_\text{cert,1-hop}$$

where $\alpha$ is the probability that tx-submission pre-diffusion is
operating normally (i.e. *not* in a catastrophic-failure regime).  Since
$P_\text{cert,full-blended} \approx 0$, the effective P_cert scales linearly
with $\alpha$.  For CUBIC at 12 MB:

| $\alpha$ | Interpretation | Effective $P_\text{cert}$ |
|--------|----------------|:-:|
| 0.99   | Pre-diffusion almost always works | 0.49 |
| 0.95   | One-in-twenty rounds catastrophic | 0.47 |
| 0.90   | One-in-ten rounds catastrophic    | 0.45 |
| 0.50   | Half-time catastrophic            | 0.25 |

(The 1-hop $P_\text{cert}$ at 12 MB is ≈ 0.497 under both Mathis and CUBIC,
so the same table applies to both models.)

**Out of scope:** estimating $\alpha$ empirically.  $\alpha$ is a
system-availability question (about the tx-submission mini-protocol's
reliability under load and adversarial conditions), not a network-model
question.  It is conceptually distinct from $\pi_1$: the empirical
$\pi_1 \approx 0.06$ measures typical per-transaction mempool divergence
during *normal* operation, while $\alpha < 1$ would represent the rate of
operationally-anomalous rounds where tx-submission has *failed* outright.
Under normal operation $\alpha \to 1$ and the headline P_cert at the 1-hop
result (≈ 0.497 under either model) is the appropriate value; quantifying
$\alpha$ during incidents requires operational data this report does not
have.

#### Maximum feasible closure when 1-hop fails (per $\pi_1$) {#max-feasible}

The intermediate regime — "1-hop fails for some voters, but the producer
itself has the txs (so full-blended is not required)" — is the most
operationally relevant question: given a realistic $\pi_1$, what is the
largest closure size still feasible if each voter's missing fraction has
to come through the blended multi-hop network?

For each $\pi_1$ in 0.05 increments, find the largest closure $S$ such that
the full voter pipeline (EB body blended + missing-fraction $\pi_1 \cdot S$
blended + CPU reapply) completes within 7 s with probability ≥ 0.75
(matching the quorum threshold):

| $\pi_1$ | Mathis $S_\text{max}$ | CUBIC $S_\text{max}$ | "naive" $S = X / \pi_1$ |
|--------:|----------------------:|---------------------:|-------------------------|
| 0.05    | **12.3 MB**           | **24.4 MB**          | M 25 MB / C 161 MB      |
| 0.10    | 7.1 MB                | 12.9 MB              | M 13 MB / C 81 MB       |
| 0.15    | 5.0 MB                | 10.1 MB              | M 8.3 MB / C 54 MB      |
| 0.20    | 3.9 MB                | 8.2 MB               | M 6.3 MB / C 40 MB      |
| 0.25    | 3.2 MB                | 6.9 MB               | M 5.0 MB / C 32 MB      |
| 0.30    | 2.7 MB                | 6.0 MB               | M 4.2 MB / C 27 MB      |
| 0.35    | 2.3 MB                | 5.3 MB               | M 3.6 MB / C 23 MB      |
| 0.40    | 2.0 MB                | 4.7 MB               | M 3.1 MB / C 20 MB      |
| 0.45    | 1.8 MB                | 4.3 MB               | M 2.8 MB / C 18 MB      |
| 0.50    | 1.6 MB                | 3.9 MB               | M 2.5 MB / C 16 MB      |

(where $X$ = max single-payload bytes such that blended diffusion alone
hits the 7 s deadline at the 75th percentile: $X = 1.25$ MB Mathis,
$X = 8.1$ MB CUBIC.  The CPU step uses the swept $\pi_1$ in
$\mu_\text{eff} = \pi_1 \mu_\text{apply} + (1{-}\pi_1) \mu_\text{reapply}$,
so per-tx cost rises with $\pi_1$.)

**The naive formula $S = X / \pi_1$ overstates feasibility by ~1.5–2×
under Mathis and ~4–7× under CUBIC** across the swept range.  It counts
only the missing-fraction fetch step; the actual voter pipeline also
spends:

- ~1–3 s on the **EB body fetch** (blended multi-hop, payload up to 512 kB
  in the generic model — a fat-tailed distribution that costs several
  seconds at the 75th percentile).
- $N \cdot \mu_\text{eff}$ on **CPU reapply**, where
  $\mu_\text{eff}$ grows from 0.092 ms/tx at $\pi_1 = 0.05$ to 0.289 ms/tx
  at $\pi_1 = 0.50$.  At $\pi_1 = 0.50$ and $S = 4$ MB this CPU step alone
  is $\approx 1.15$ s.

These overheads consume a substantial fraction of the 7 s budget *before*
the missing-fraction fetch even starts, leaving much less than $X$ for the
$\pi_1 \cdot S$ transfer.  The naive-vs-realistic ratio is *largest* at
small $\pi_1$, where the larger feasible $S$ produces a heavier CPU step
and a larger absolute EB-body overhead relative to a budget that the
naive formula treats as all-fetch.

**What this means practically.**

- **At the empirical mean $\pi_1 \approx 0.06$**: under the blended-missing
  case the max feasible closure is ≈ **11 MB Mathis, 20 MB CUBIC**.  CUBIC
  comfortably exceeds the 12 MB CIP target; Mathis sits just below it.
- **At the empirical worst-pair $\pi_1 \approx 0.085$**: max feasible
  is ≈ **8 MB Mathis, 14 MB CUBIC**.  CUBIC still exceeds 12 MB;
  Mathis falls short.
- **At $\pi_1 = 1/6 \approx 0.17$ (the prior Haskell model's default)**:
  max feasible drops to ≈ **4.6 MB Mathis, 9.4 MB CUBIC** — both
  models fall short of the 12 MB target.
- **At $\pi_1 \geq 0.30$**: max feasible is ≈ **2.7 MB Mathis, 6 MB CUBIC**
  — well short of the 12 MB target under either model.

Combined with the §5.1 1-hop headline (12 MB at the Praos cap under both
models for empirical $\pi_1$), the picture is: under the **1-hop**
approximation the 12 MB CIP target is robustly feasible under both
models, but if the missing fetch falls back to **blended multi-hop**, only
CUBIC retains comfortable headroom (≈ 20 MB at $\pi_1 \approx 0.06$,
≈ 14 MB at $\pi_1 \approx 0.085$) — Mathis sits at or just below
12 MB across the empirical range, and both models fall short once
$\pi_1$ rises to the prior Haskell model's default of 1/6.
The 1-hop fetch path (the upstream peer holds the missing transactions
locally) is therefore an important operational invariant, separate from
the stronger pre-diffusion-failure scenario covered by the full-blended
case above.

### 5.4 Network Model Sensitivity (Mathis vs CUBIC vs loss rate)

The plot `plots/network_model_comparison.svg` shows the two-panel comparison:
- *Left:* steady-state throughput vs $p$ for short / medium / long distances,
  for both Mathis and CUBIC.  CUBIC's flatter response ($p^{-3/4}$ vs Mathis
  $p^{-1/2}$) gives ~11× more throughput at $p = 10^{-4}$ across all distances.
- *Right:* transfer time for a 2 MB long-haul fetch (the missing-closure
  load at $S_{EB-tx} = 12$ MB) vs $p$, with the 7 s voter deadline marked.

**Where each model crosses the 7 s deadline.**  Solving $T_\text{2MB,long}(p) = 7$
seconds for each model:

| Throughput model | $p$ at which 2 MB long-haul = 7 s |
|------------------|-----------------------------------|
| Mathis           | $\approx 2.8 \times 10^{-4}$      |
| CUBIC            | $\approx 4.6 \times 10^{-3}$      |

Below each $p$ value, the missing-closure fetch finishes in time and the
quorum holds at 12 MB.  Above, $P_\text{validating}$ drops below 0.75 and
the quorum cliff appears.  The analysis default $p = 10^{-4}$ lies **well
below both** crossings: the cliff is absent under both Mathis and CUBIC,
with substantial margin.

#### Caveats common to both models

Several real-world effects are *not* captured by either steady-state
throughput equation and may matter more than the Mathis-vs-CUBIC distinction:

1. **Receiver window (rwnd) and BDP.**  Effective throughput is bounded by
   $\min(W_\text{cwnd}, W_\text{rwnd})/\text{RTT}$.  Linux default rwnd is
   4–16 MB after autotuning, comfortably above either model's steady-state
   $W_\text{cwnd}$ at $p = 10^{-4}$ — but a freshly opened connection or a
   long-idle one may start with a much smaller rwnd that lags the
   congestion-control prediction.

2. **Slow start is modeled, but real-world TCP exhibits additional effects
   this model omits.**  The diffusion-time table *does*
   simulate slow start explicitly: cwnd starts at $\text{cwnd}_0 = 10$ MSS
   ($14{,}600$ B) and doubles each RTT until it hits the model-specific cap
   $W_\text{ss}$, identically under both Mathis and CUBIC.  The model choice
   therefore only changes the transfer time once the connection has *cleared*
   slow start.  Tracing the cwnd-doubling sequence from $\text{cwnd}_0$
   (values in bytes; kiB = 1024 B; "—" = same as Mathis column):

   | Round | Mathis cwnd | Mathis cum sent | Mathis status | CUBIC cwnd | CUBIC cum sent | CUBIC status |
   |-------|-------------|-----------------|---------------|------------|----------------|--------------|
   | 1     | 14 600      | 14 600          | slow start    | —          | —              | slow start   |
   | 2     | 29 200      | 43 800          | slow start    | —          | —              | slow start   |
   | 3     | 58 400      | 102 200         | slow start    | —          | —              | slow start   |
   | 4     | 116 800     | **219 000**     | slow start    | —          | **219 000**    | slow start   |
   | 5     | **146 000** (capped) | 365 000 | **capped**   | 233 600 (160 MSS) | 452 600 | slow start   |
   | 6     | 146 000     | 511 000         | steady state  | 467 200    | 919 800        | slow start   |
   | 7     | 146 000     | 657 000         | steady state  | 934 400    | **1 854 200**  | slow start   |
   | 8     | 146 000     | 803 000         | steady state  | **1 538 590** (capped) | 3 392 790 | **capped** |

   Mathis caps at the end of round 4 (cwnd $\to W_\text{ss}^M = 146$ kB);
   CUBIC caps at the end of round 7 (cwnd $\to W_\text{ss}^C \approx 1.54$
   MB).  The asymptotic per-RTT throughput ratio is $W_\text{ss}^C /
   W_\text{ss}^M \approx 10.5$.

   Concrete consequences for our analysis (transfer-size thresholds in
   bytes, with approximate kiB/MiB labels):

   - **Transfers $\leq 365{,}000$ B ($\approx 356$ kiB, or $0.365$ MB
     decimal) give identical times under Mathis and CUBIC.**  The flow
     ends in rounds 1–5 with the same number of rounds and the same
     final-round bytes-sent.  This covers the small EB-body fetches and
     the 1-hop missing-closure fetches at $S_{EB-tx} \leq 1$ MB, which
     is why the two models agree at low closure sizes in §5.1.

   - **Transfers $365{,}000$ B – $1{,}854{,}200$ B ($\approx 356$ kiB –
     $1.77$ MiB) diverge** because Mathis sends a fixed $146$ kB/RTT
     while CUBIC continues to double its cwnd.  Mathis needs more rounds
     than CUBIC.  This covers EB-body fetches at the upper end of the
     $\{1, 64, 256, 512\}$ kB mixture and the missing-closure fetches at
     $S_{EB-tx} \in [4, 8]$ MB.

   - **Transfers $> 1{,}854{,}200$ B ($\approx 1.77$ MiB) exercise both
     caps.**  Beyond this size, every additional MB of payload costs
     ~$1/146$ RTTs under Mathis vs ~$1/1538$ RTTs under CUBIC, so the
     transfer-time ratio approaches the asymptotic $10.5$ as size grows.  At $S_{EB-tx} = 12$ MB the missing-closure fetch is $2$ MB,
     so the per-model transfer-time gap is at its largest in the
     analysis ($\approx 4.4$ s Mathis vs $\approx 2.0$ s CUBIC) — but
     both still fit within the 7 s voter deadline, which is why
     $P_\text{cert}$ at 12 MB is identical (≈ 0.497, Praos cap) under
     both models in §5.1.

   Real-world slow-start effects *not* captured by either model:

   - *Idle restart (RFC 5681 §4.1).*  A TCP connection idle for more than
     one RTO resets cwnd to $\text{cwnd}_0$.  Between EB events, long-lived
     SPO connections may pay the slow-start cost each time.
   - *HyStart / HyStart++ (RFC 9406).*  Linux exits slow start before
     reaching the formal $W_\text{ss}$ when it detects ACK-train
     compression, giving a smaller effective cap than the model assumes.
   - *Initial RTO of 1 s (RFC 6298).*  A packet lost during the first
     1–2 RTTs triggers a 1 s timeout, far slower than the model's smooth
     doubling.  This is rare at $p = 10^{-4}$ but expected at higher loss.
   - *ACK clocking variance.*  The model treats each RTT as a discrete
     burst of `cwnd` bytes; real TCP paces transmissions across the RTT,
     which interacts with bufferbloat (caveat 3) and can stall in
     reordered or coalesced-ACK scenarios.

3. **Bufferbloat on the bottleneck link.**  A deep bottleneck queue keeps
   the RTT estimate stale and inflates the effective in-flight bytes,
   producing throughput well below either model's prediction.  This is a
   real concern for SPOs using consumer-grade uplinks.

4. **The $p = 10^{-4}$ default is generous.**  CUBIC's advantage shrinks
   rapidly with higher $p$: at $p = 10^{-2}$ the gap is ~3×, and at
   $p > 10^{-2}$ both models predict similarly poor throughput.  Reported
   end-to-end loss on intercontinental paths under load can reach the
   $10^{-3}$ to $10^{-2}$ range during bursty cross-traffic; direct
   measurements on SPO paths are not currently available.

5. **CUBIC has a TCP-friendly mode.**  At high $p$ or with competing Reno
   flows on the same path, real CUBIC implementations explicitly fall back
   to a Reno-friendly cwnd schedule to play fair.  In that regime Mathis is
   the *more* faithful model.

The recommended interpretation: **CUBIC is the Linux-kernel default and
the realistic model for well-tuned modern paths; Mathis is the
conservative Reno/AIMD bound that applies to congested, rwnd-limited, or
CUBIC-Reno-friendly-fallback regimes.  Realistic SPO performance falls
between them, weighted toward CUBIC under healthy conditions and toward
Mathis under stress.**

### 5.5 TxCache Miss Rate Sensitivity (π₁ sweep) {#pi1-sensitivity}

The default cache miss rate $\pi_1 = 1/6 \approx 0.17$ is inherited from a
two-state Markov chain in the prior Haskell ΔQ model whose parameters
$(p = 0.5,\, q = 0.9)$ were chosen without empirical derivation.  We have
since extracted an **empirical estimate from the
[mempool-measurements](https://github.com/input-output-hk/ouroboros-leios/tree/main/post-cip/mempool-measurements)
dataset** (see `pi1_derivation.md`):

| Source | $\pi_1$ |
|--------|---------|
| Prior model (hand-chosen Markov) | **0.167** |
| Empirical mean (cross-region BAU) | **0.06** |
| Empirical worst-case pair | **0.085** |
| Empirical range | [0.02, 0.09] |

The prior value is **~3× the empirical mean**.  The missing-closure fetch
size scales linearly with $\pi_1$, so in principle the quorum cliff
location depends on this choice — but as the sweep below shows, every
$\pi_1$ in the empirical-and-prior range gives identical $P_\text{cert}$
at the Praos cap, and sensitivity to $\pi_1$ only emerges in the extreme
tail ($\pi_1 \geq 0.50$ under Mathis).

To bound the uncertainty, we sweep $\pi_1 \in \{0.05,\, 0.10,\, 1/6,\, 0.30,\, 0.50\}$
under both network models.  The sweep brackets the empirical estimate
between the 0.05 and 0.10 points; the 1/6 point corresponds to the prior
assumption; 0.30 and 0.50 represent adversarial / severe-fragmentation
scenarios.  Plot: `plots/pi1_sensitivity.svg`.

*Note on the scenario.* This sweep uses the **1-hop** missing-closure
fetch (the default voter pipeline, in which cache-miss voters fetch the
missing $\pi_1 \cdot S$ from their upstream peer in a single hop).  The
companion table in §5.3 (max feasible $S$ vs $\pi_1$) gives the
corresponding numbers under the **blended-missing** fall-back, where the
missing fraction must traverse the full multi-hop network — that case
is materially more restrictive (12 MB is feasible under CUBIC at the
empirical mean $\pi_1$ but not under Mathis).

**P_cert at selected $S_{EB-tx}$, per model and π₁:**

*Mathis*

| π₁      | 1 MB      | 4 MB      | 8 MB      | 12 MB     |
|---------|-----------|-----------|-----------|-----------|
| 0.05    | 0.497     | 0.497     | 0.497     | 0.497     |
| 0.10    | 0.497     | 0.497     | 0.497     | 0.497     |
| **1/6** | **0.497** | **0.497** | **0.497** | **0.497** |
| 0.30    | 0.497     | 0.497     | 0.497     | 0.497     |
| 0.50    | 0.497     | 0.497     | 0.451     | 0.000     |

*CUBIC*

| π₁      | 1 MB      | 4 MB      | 8 MB      | 12 MB     |
|---------|-----------|-----------|-----------|-----------|
| 0.05    | 0.497     | 0.497     | 0.497     | 0.497     |
| 0.10    | 0.497     | 0.497     | 0.497     | 0.497     |
| **1/6** | **0.497** | **0.497** | **0.497** | **0.497** |
| 0.30    | 0.497     | 0.497     | 0.497     | 0.497     |
| 0.50    | 0.497     | 0.497     | 0.497     | 0.497     |

**Three observations from the sweep:**

1. **At every $\pi_1 \leq 1/6$ (covering both empirical and prior-model
   defaults), 12 MB is comfortably feasible under both models** —
   $P_\text{cert}$ at the Praos cap everywhere.  The 1-hop missing-fetch
   at empirical-or-conservative miss rates leaves substantial margin.

2. **At $\pi_1 = 0.30$, all sizes up to 12 MB still hit the Praos cap.**
   The missing-fetch overhead has grown but not enough to fail the 7 s
   voter deadline at any tested CIP-target size.

3. **Only at $\pi_1 = 0.50$ does Mathis fail at 12 MB** ($P_\text{cert} \to
   0$).  CUBIC is robust to $\pi_1$ all the way up to 0.50 at 12 MB.

**Implication.** **Neither the throughput model nor $\pi_1$ (within the
empirical and prior-model range) is a sensitive input to the 12 MB
conclusion** — the Praos cap is the only binding limit across the entire
matrix below $\pi_1 = 0.50$.

**What this means for the CIP-0164 12 MB target.**

- **At the empirical mean ($\pi_1 \approx 0.06$):** 12 MB feasible under
  either model at the Praos cap.
- **At the empirical worst-pair ($\pi_1 \approx 0.085$):** same conclusion.
- **At the prior model's default $\pi_1 = 1/6 \approx 0.17$:** 12 MB still
  feasible under both models.
- **At a hypothetical heavy-load incident with $\pi_1 = 0.30$ or 0.50:**
  CUBIC remains feasible; Mathis only fails at $\pi_1 = 0.50$.

The empirical evidence therefore supports the 12 MB target under normal
operation with substantial margin.  The relevant residual risk is **how
high $\pi_1$ can spike during congestion incidents** (the unexplained
high-utilization outlier from the us-east-2 monitoring node, where
$\pi_1$ rose to ≈ 0.44 on blocks at > 85% utilization, is a cautionary
anecdote; see `pi1_derivation.md` §3) — but even at $\pi_1 = 0.44$ CUBIC
gives $P_\text{cert}$ at the Praos cap.

The single most useful next measurement would be **a $\pi_1$ estimate
from a broader SPO sample** (not just three AWS regions) covering more
network topologies and a wider time window including incident periods,
ideally fitting the Markov chain $p, q$ directly from the observed
tx-arrival autocorrelation rather than just the steady-state mean.

---

## 6. Comparison with Prior Analysis

| Aspect                      | Prior model                         | Improved model              |
|-----------------------------|-------------------------------------|-----------------------------|
| RB structure                | Both tx + cert paths forced always  | Probabilistic choice p_cert |
| EB closure size (model)     | Implicit; N=2500 hardcoded          | Explicit sweep 0–12 MB      |
| Reapply distribution        | Scale mixture U(1,N): mean N/2 txs  | Fixed-N CLT: exactly N txs  |
| EB closure fetch            | Not modelled (TxCache only)         | 1-hop bulk transfer         |
| Certification probability   | Not computed; assumed fixed         | Computed from quorum model  |
| Per-tx apply time           | 10.60 ms (per-block mean)           | 0.507 ms/tx (tx-weighted)   |
| Per-tx reapply time         | 2.71 ms (per-block mean)            | 0.070 ms/tx (tx-weighted)   |
| Network transfer model      | Empirical Praos table (≤2 MB data)  | TCP slow-start + selectable steady-state (Mathis / CUBIC) |
| P(≤14s) in prior model      | 0.9740 (single point)               | Not directly comparable (different RB structure) |
| P_cert at 12 MB (Mathis)    | Not computed                        | 0.497 (at Praos cap)        |
| P_cert at 12 MB (CUBIC)     | Not computed                        | 0.497 (at Praos cap)        |

The prior analysis reported P(≤14s) = 0.974 for its (incorrect)
single-scenario model, which was cited as validation of the CIP parameters.
That figure was inflated by three independent errors: (a) the scale mixture
underestimating reapply time by 2×; (b) the RB structure bug mixing
mutually exclusive paths; and (c) the per-tx timing constants being
per-block means rather than per-tx costs (≈ 20–40× overstatement).

Under fully corrected assumptions, the CIP target of 12 MB is **robustly
feasible under both Mathis and CUBIC** at $\pi_1 = 1/6$ and below: CPU is
non-binding (single-core ceiling ≈ 38 MB); the 2 MB missing-closure fetch
over 268 ms RTT (long-haul) takes ≈ 4.4 s under Mathis and ≈ 2.0 s under
CUBIC — both within the 7 s voter deadline.  $P_\text{validating} \geq 0.95$
under either model, $P_\text{quorum} \approx 1.0$, and $P_\text{cert}$
stays at the Praos cap of $\approx 0.497$.

---

## 7. Limitations and Assumptions

1. **1-hop approximation for EB closure fetch.** The model assumes each node
   can obtain missing transactions from its upstream peer in a single hop.
   If the raw transactions making up the closure have *not* pre-diffused via
   tx-submission (e.g., under adversarial withholding or heavy load), the full
   closure must traverse the blended multi-hop network.  At 12 MB this
   full-blended diffusion succeeds within 14 s only **14%** of the time under
   Mathis and **99%** under CUBIC (§5.2).  The corresponding voter pipeline
   still yields $P_\text{cert} \approx 0$ under either model — the 7 s voter
   deadline and 75% quorum threshold are both tighter than the 14 s network
   delivery alone, so even CUBIC's near-100% network-delivery rate doesn't
   prevent the quorum failure.  See **§5.3 "Full-blended worst case"** for
   the full derivation and the $\alpha$-mixture formulation.  The 1-hop
   model is only valid when pre-diffusion via tx-submission is effective.

2. **Average transaction size = 1 kB.** The CIP uses 2 kB in some places. At
   2 kB/tx, a 12 MB closure has half as many tx hashes (so a smaller EB
   body) and half the missing-closure-fetch size for cache misses.  Since
   12 MB is already feasible at 1 kB/tx, the 2 kB/tx case
   would only widen the feasibility margin.

3. **Single scalar $\pi_1$ rather than a Markov chain fit.**  §5.5 and
   `pi1_derivation.md` now provide an empirically-derived steady-state
   value ($\pi_1 \approx 0.06$ cross-region BAU mean, 0.085 worst-pair),
   replacing the prior model's hand-chosen $p = 0.5,\, q = 0.9$ Markov
   parameters (which yielded $\pi_1 = 1/6$).  What remains a limitation is
   that we use the steady-state mean only, without re-fitting the
   underlying $(p, q)$ to the tx-arrival time series — temporal
   stickiness in mempool divergence is therefore not captured.  §5.5
   sweeps $\pi_1$ to bound the residual uncertainty.

4. **Fixed binary miss fraction — no heterogeneity across nodes.**
   The TxCache model collapses to a single constant: each node is either a
   *cache hit* (probability $\pi_2 = 5/6$, holds the full closure, 1 ms lookup)
   or a *cache miss* (probability $\pi_1 = 1/6$, must fetch exactly
   $\pi_1 \cdot S_{EB-tx}$ from one hop).  There is no state in between.
   In reality, nodes have a continuous distribution of miss fractions depending
   on network position, uptime, and mempool composition; in particular, a node
   with a cold or empty mempool could be missing the **entire** closure.

   For the CIP-0164 target $S_{EB-tx} = 12$ MB, the assumed cache-miss
   fetch is $\pi_1 \times 12\,\text{MB} \approx 2\,\text{MB}$.  A node
   missing 100% of the closure would instead need to fetch the full
   12 MB — approximately 6× more data.  Over a long-haul link this 1-hop
   transfer takes ≈ 3.6 s under CUBIC and ≈ 23.7 s under Mathis;
   combined with the EB body fetch (~1 s blended) and CPU reapply
   (~1.8 s), a cold-mempool node sits at ~6.5 s total under CUBIC
   (tight but inside the 7 s deadline) and well over the deadline under
   Mathis.  The fixed-fraction assumption therefore overstates
   feasibility for cold-mempool nodes under Mathis; under CUBIC the
   margin is narrower but the cold-node case is still mostly
   recoverable.

5. **No adversarial behaviour.** The model assumes honest nodes that always
   diffuse transactions promptly via tx-submission before the EB is produced.
   An adversary that deliberately withholds transactions from tx-submission
   invalidates the 1-hop approximation and could force the full multi-hop
   diffusion scenario, reducing the feasible range significantly.

6. **TCP throughput model assumptions.**
   The transfer-time model uses TCP slow start from $\text{cwnd}_0 = 10$ MSS
   (14 600 B), capped at a model-specific steady-state window $W_\text{ss}$
   (Mathis: 146 000 B; CUBIC: 1 538 590 B at $p = 10^{-4}$).  Common
   assumptions:

   - *MSS = 1460 B, cwnd₀ = 10 MSS.*  Modern Linux kernels use IW10 (RFC 6928);
     TLS adds a 5-byte record header reducing effective MSS slightly.  Idle-
     restart and connection reuse can lower the effective cwnd₀.
   - *One-way delays.*  Short (6 ms), medium (34.5 ms), and long (134 ms),
     derived from Table 1 of the Praos paper (`PraosModel.pdf`) which gives
     RTTs of 12 / 69 / 268 ms for these distance categories (we halve to
     get OWDs).  The long RTT (268 ms) reflects typical intercontinental
     paths; true 95th-percentile South America–Asia-Pacific paths (which
     have no direct undersea cable) may reach 300–400 ms RTT, so the long
     category is mildly optimistic for that specific worst case.  A higher
     OWD increases the number of slow-start RTTs before reaching
     $W_\text{ss}$ and dominates transfer time for large sizes.
   - *1 Gbit/s interface cap.*  Applies only if the interface is the
     bottleneck; SPO nodes with lower-bandwidth connections would see worse
     numbers.  The bandwidth-delay product $\text{BDP} = 125\,\text{MB/s}
     \times \text{RTT}$ is well above either model's $W_\text{ss}$ at
     $p = 10^{-4}$ on every distance category, so the BDP cap is inactive.
   - *Persistent TCP, no handshake.*  Each fetch is assumed to use an existing
     long-lived TLS connection; cold-start RTTs (TCP 3-way + TLS handshake)
     are not included.

   Both throughput models share these assumptions; they differ only in the
   functional form of $W_\text{ss}$ (Mathis: $\propto p^{-1/2}$; CUBIC:
   $\propto p^{-3/4}$).  See §5.4 for the loss-rate sensitivity and the
   five real-world caveats (rwnd lag, short-flow slow-start dominance,
   bufferbloat, $p$ at high-traffic SPO paths, CUBIC's Reno-friendly fallback)
   that further blur the boundary between the two models.

   The full-blended diffusion results at $S_{EB-tx} > 4$ MB are the most
   model-sensitive: at 12 MB, $P(\leq 14\,\text{s})$ is 14% under Mathis
   and 99% under CUBIC.

7. **No FFD (Freshest First Delivery).** Following the prior report, FFD is
   not modelled; in practice it can delay older EBs in favour of newer ones.

8. **The voting deadline computation uses `3·L_hdr + L_vote = 7s`.** This
   implies three pipeline stages each requiring L_hdr = 1 slot before the voter
   can start. If the actual voter deadline is shorter (e.g., `L_hdr + L_vote =
   5s`), the feasible S_EB_tx is correspondingly smaller.

---

## 8. Recommendations

1. **The CIP-0164 target of 12 MB is robustly feasible under realistic
   mainnet conditions.**  At the empirical $\pi_1 \approx 0.06$ (§5.5,
   `pi1_derivation.md`) and the Praos paper's RTT values, $P_\text{cert}
   \approx 0.497$ at 12 MB under *both* Mathis and CUBIC.  The 2 MB
   missing-closure fetch over long-haul (268 ms RTT) takes ≈ 4.4 s under
   Mathis and ≈ 2.0 s under CUBIC — both well within the 7 s voter deadline.
   The throughput-model uncertainty is immaterial in this regime; both
   models reach the Praos cap at every CIP-target size, and even at
   $\pi_1 = 1/6$ (the prior Haskell model's default), 12 MB remains
   feasible.

2. **CPU is not the binding constraint at any closure size ≤ 12 MB.**  With
   corrected per-tx costs ($\mu_\text{eff} = 0.143$ ms/tx), the single-core
   CPU ceiling is ≈ 38 MB on commodity hardware.  No special CPU provisioning
   is required for EB closure validation in this model (multi-core
   parallelism is out of scope).

3. **Ensure effective tx-submission pre-diffusion.**  The model's main
   remaining load-bearing assumption is the 1-hop approximation: transactions
   have already diffused via tx-submission before the EB is produced.  Under
   total pre-diffusion failure the effective $P_\text{cert}$ collapses to
   ≈ 0 under either throughput model at 12 MB (the 7 s voter deadline and
   75% quorum threshold both fail, regardless of whether the network
   delivers within 14 s; see §5.3 "Full-blended worst case" and the
   $\alpha$-mixture formula $P_\text{cert,effective} \approx \alpha \cdot
   P_\text{cert,1-hop}$).  Protocol parameters and node implementation
   must ensure pre-diffusion holds under normal operation.

4. **The Praos interruption probability (≈ 50%) is a hard ceiling.**
   No tuning of $S_{EB-tx}$, throughput model, or network topology
   can push $P_\text{cert}$ above ≈ 0.497 whenever quorum is met.  If higher
   certification rates are desired, the relationship between the Leios round
   length and the Praos slot rate needs revisiting.

5. **Measure the actual network conditions on the SPO mesh.**  The Mathis-vs-
   CUBIC gap is a useful proxy for our uncertainty about real-world TCP
   throughput.  Three measurements would narrow the band:
   - 95th-percentile SPO-to-SPO one-way delays (currently assumed 268 ms long-haul).
   - End-to-end packet loss on intercontinental SPO paths (currently $p = 10^{-4}$).
   - Effective receive-window autotuning state for typical SPO connections.
   See §5.4 for the corresponding loss-rate sensitivity.

6. **Adopt the empirical $\pi_1$ estimate.**  An empirical extraction from
   `post-cip/mempool-measurements/` (see `pi1_derivation.md`) gives
   $\pi_1 \approx 0.06$ (cross-region mean, BAU window) with a worst-pair
   value of 0.085.  The prior model's $\pi_1 = 1/6$ is **~3× too high**.
   At the empirical value, §5.5 shows 12 MB is feasible under either
   throughput model.  Two outstanding tasks:
   - Confirm whether the unexplained high-utilization outlier from the
     us-east-2 monitoring node ($\pi_1 \approx 0.44$ on blocks at > 85%
     utilization) reflects a real incident or a measurement artifact.
   - Broaden the measurement beyond three AWS regions; SPOs on
     consumer-grade uplinks or at mesh-edge positions may have higher
     miss rates than the well-connected datacentre instrumentation.

7. **Verify the average transaction size assumption.**  At 2 kB/tx rather
   than 1 kB/tx, the missing-closure fetch at 12 MB halves to 1 MB.  Since
   12 MB is already feasible at 1 kB/tx, the 2 kB/tx case
   only widens the margin.

8. **Re-examine the per-tx timing constants with a richer dataset.**  The
   corrected values are transaction-weighted means from mainnet blocks with at
   most 385 transactions.  Extrapolating to EB closures of thousands of
   transactions assumes the same per-tx cost distribution, which may not hold
   if closure composition differs from mainnet blocks.

---

## 9. Plot Guide

Plots are organised into three groups:

- `plots/network_model_comparison.svg` — top-level, model-agnostic loss-rate
  sensitivity plot (§5.4).
- `plots/pi1_sensitivity.svg` — top-level π₁ sensitivity plot (§5.5).
- `plots/mathis/…` — full set of analysis plots produced under the Mathis
  steady-state throughput model.
- `plots/cubic/…` — same set produced under the CUBIC steady-state model.

Each model directory contains 7 SVGs (the suite documented below).  The
descriptions below apply to the named plot in either model directory; where
the per-model conclusion differs, both are noted.

---

### `network_model_comparison.svg` *(top-level, both models)*

**What it shows.** Two panels, side by side:
- *Left* — steady-state TCP throughput vs packet-loss probability $p$, plotted
  on log–log axes for each of the three distance categories under both Mathis
  ($T \propto p^{-1/2}$, solid) and CUBIC ($T \propto p^{-3/4}$, dashed).
  The 1 Gbit/s interface cap and the analysis default $p = 10^{-4}$ are marked.
- *Right* — transfer time for a 2 MB long-haul (OWD = 268 ms) fetch vs $p$
  (semilog), with the 7 s voter deadline marked.  This is the
  missing-closure load at $S_{EB-tx} = 12$ MB.  Annotation arrows show
  approximately where each model crosses the deadline.

**Why it matters.** Quantifies how much loss-rate headroom each model has
before hitting the 7 s deadline.  The 2 MB fetch hits the 7 s deadline at
$p \approx 2.8 \times 10^{-4}$ under Mathis and $\approx 4.6 \times 10^{-3}$
under CUBIC — both *above* the analysis default of $10^{-4}$, so the
12 MB cliff is absent under either model at default $p$.  Mathis tolerates
~2.8× higher loss before falling off the cliff; CUBIC tolerates ~46×.

---

### `pi1_sensitivity.svg` *(top-level, both models)*

**What it shows.** Two side-by-side panels (Mathis | CUBIC).  In each panel,
$P_\text{cert}$ vs $S_{EB-tx}$ is plotted as a family of curves, one per
TxCache miss rate $\pi_1 \in \{0.05,\, 0.10,\, 1/6,\, 0.30,\, 0.50\}$.  The
default $\pi_1 = 1/6$ curve is highlighted (thicker, solid); others are
dashed.  The horizontal red dotted line marks the Praos cap
$P_\text{cert} \approx 0.497$.

**Why it matters.** Shows how the quorum cliff (or lack thereof) shifts
with the assumed mempool-fragmentation rate.  **No cliff appears in the
0–12 MB range at any $\pi_1 \leq 1/6$** under either model.  The cliff
only appears for Mathis at $\pi_1 = 0.50$; CUBIC remains feasible at
every tested $\pi_1$ across the full sweep.

---

### `compare_models.svg`

**What it shows.** Four CDF curves plotted on the same axis, all representing
$P(\text{RB fully processed} \leq t)$:
- *Existing model (broken)* — replicates the prior Haskell analysis.
- *Improved, $S_{EB-tx}=0$* — improved model with no EB closure (baseline).
- *Improved, $S_{EB-tx}=12\,\text{MB}$* — improved model at the CIP target size.
- *txRB path only* — the non-cert branch (RB carries transactions, no EB).

The vertical dashed red line marks the 14-second deadline.

**Why it matters.** The prior model's CDF crosses the deadline at ~0.97,
which was used to validate the CIP parameters.  Under the new model both
the Mathis and CUBIC 12 MB CDFs plateau at $\approx 0.497$ — at the Praos
cap, no cliff.  The chart illustrates that the model corrections change
the interpretation fundamentally: what previously appeared to be a
feasibility limit at 0.974 is now revealed as the Praos 50% cap.

**Counterintuitive appearance — blue below orange.** The $S_{EB-tx}=0$ curve
(blue) sits *below* the $S_{EB-tx}=12\,\text{MB}$ curve (orange) at early
times, which looks backwards at first glance.  Both curves show the
*combined* round outcome:

$$\text{cdf\_comb}(t) = p_\text{cert} \times \text{certRB}(t) + (1-p_\text{cert}) \times \text{txRB}(t)$$

At $S_{EB-tx}=0$, $p_\text{cert} \approx 0.50$, so half of all rounds take the
certRB path, which requires fetching the EB body (up to 512 kB, blended
multi-hop) even when the closure is empty.  That diffusion overhead pulls the
$S_{EB-tx}=0$ curve below the $S_{EB-tx}=12\,\text{MB}$ curve at early times.

This is not an error.  It correctly reflects a real protocol cost: running
Linear Leios with active EB certification makes the average round *slower* than
pure Praos (txRB only), because cert rounds carry more network overhead.  The
green dotted *txRB path only* curve closely tracks the 12 MB curve, confirming
that the 12 MB result is dominated by the fast txRB path (50% of rounds).

---

### `eb_closure_sweep.svg`

**What it shows.** A grid of CDF curves — one per simulated $S_{EB-tx}$ value
from 0 to 12 MB.  Two subplots cover (left) the certRB path CDF and (right)
the combined outcome CDF.  Curves are colour-coded by size; the vertical line
marks the 14-second deadline.

**Why it matters.** With the corrected per-tx constants and the corrected
Praos RTTs, every curve from 0 to 12 MB plateaus at $P_\text{cert} \approx
0.497$ before the 14-second deadline under both throughput models —
$P_\text{validating}$ is high enough at every CIP-target size that the
quorum is comfortably met.  No cliff appears in the plotted range under
either model.

---

### `feasibility.svg`

**What it shows.** Two subplots vs $S_{EB-tx}$:
- *Left* — three probability curves: $P_\text{cert}$ (liveness), $P(\text{certRB} \leq 14s)$ (safety), and their product $P_\text{cert} \times P(\leq 14s)$ (the combined outcome, the only quantity that matters for protocol correctness).
- *Right* — $P(\text{certRB validated} \leq 14s \mid \text{cert path})$ alone, zoomed to show whether the certRB diffusion time is a bottleneck.

**Why it matters.** Both panels stay essentially flat at $P_\text{cert}
\approx 0.497$ across the entire 0–12 MB range under either model.  The
"cert × safe" composite likewise stays at ≈ 0.497 throughout.  Confirms
the Praos cap is the only binding limit in the CIP target range — no
network-driven cliff appears under either model.

---

### `certification.svg`

**What it shows.** Two subplots vs $S_{EB-tx}$:
- *Left* — the three components of $P_\text{cert}$: $P_\text{validating}$
  (voter pipeline ≤ 7s), $P_\text{quorum}$ (≥ 450 votes collected), and
  $P_\text{cert}$ itself.  $P_\text{interrupted}$ (≈ 0.503) is a constant cap
  annotated as a horizontal band.
- *Right* — quantiles (Q50, Q75, Q95) of the certRB completion time vs
  $S_{EB-tx}$, showing how the tail of the distribution shifts.

**Why it matters.**
- *Mathis*: $P_\text{validating}$ declines from ≈ 1.000 at 0 MB to 0.948 at
  12 MB — always well above the 0.75 quorum threshold.  $P_\text{quorum}
  \approx 1.0$ throughout; $P_\text{cert}$ stays at the Praos cap.
- *CUBIC*: $P_\text{validating}$ declines from ≈ 1.000 at 0 MB to 0.992 at
  12 MB.  Same conclusion: $P_\text{cert}$ at the Praos cap.

The right panel (Q50/Q75/Q95 quantiles) shows slowly increasing tails as
closure size grows in both models, driven by the longer voter pipeline.

---

### `outcome_diagram.svg`

**What it shows.** A schematic (non-data) flow diagram of the two mutually
exclusive RB validation paths.  With probability $p_\text{cert}$ the RB is a
*certRB*: the node downloads the small RB header, fetches the EB body, applies
(or reapplies) the EB closure transactions, and verifies the certificate.  With
probability $1 - p_\text{cert}$ the RB is a *txRB*: the node downloads the
header and a ≤ 90 kB transaction payload and applies those transactions
directly.

**Why it matters.** This diagram is the visual summary of Bug Fix 1 (Section 3).
The prior model forced *both* paths to run in parallel on every RB; this
diagram illustrates why that was wrong and what the correct probabilistic
choice model looks like.

---

### `sensitivity_1hop_vs_blended.svg`

**What it shows.** CDF curves for the full certRB-path pipeline at
$S_{EB-tx} = 12\,\text{MB}$, under two assumptions about how missing
transactions are fetched:
- *1-hop* — each node fetches only the missing fraction ($\pi_1 \cdot S$)
  from its upstream peer (1 network hop).
- *Blended* — missing transactions must traverse the full blended multi-hop
  network model.

**Why it matters.**
- *Mathis*: 1-hop and blended both give $P_\text{cert} = 0.497$ (Praos
  cap).  $P_\text{validating}$ drops from 0.948 (1-hop) to 0.854
  (blended) but stays above the quorum threshold.
- *CUBIC*: 1-hop and blended both give $P_\text{cert} = 0.497$.
  $P_\text{validating}$ drops from 0.992 (1-hop) to 0.942 (blended).

The 1-hop vs blended-missing distinction is not feasibility-relevant in
the 0–12 MB range: both pathways succeed.  The plot confirms the
small-but-real $P_\text{validating}$ gap between 1-hop and blended
without it changing the certification outcome.

---

### `network_diffusion.svg`

**What it shows.** A network-only (CPU excluded) analysis across $S_{EB-tx}$
values from 0.5 MB to 12 MB.  Three $P(\leq t)$ curves are shown for each
size: 1-hop fetch of missing fraction (EB body + 1-hop), blended fetch of
missing fraction (EB body + blended multi-hop), and full blended diffusion of
the entire closure.  The 7-second voter deadline and 14-second total deadline
are annotated.

**Why it matters.** This plot answers the question "even if the CPU were
infinitely fast, could the network deliver the closure in time?"  All
three curves assume *every* voter must fetch (i.e. treat all voters as
cache-miss); this is therefore strictly more conservative than the
§5.1 voter pipeline, where 5/6 of voters are cache-hits with a near-zero
lookup.
- *Mathis*: full-blended at 12 MB gives $P(\leq 14\,\text{s}) = 0.139$ —
  the network delivers only 14% of the time under the worst-case
  no-pre-diffusion assumption.  The 1-hop scenario at 12 MB gives
  $P(\leq 7\,\text{s}) \approx 0.933$ (essentially feasible).
- *CUBIC*: full-blended at 12 MB gives $P(\leq 14\,\text{s}) = 0.991$ —
  essentially feasible even without pre-diffusion.  1-hop at 12 MB gives
  $P(\leq 7\,\text{s}) \approx 0.999$.

The 1-hop scenario is feasible under either model at every CIP-target
size.  The full-blended worst case still distinguishes the models —
Mathis fails, CUBIC succeeds on the network delivery alone — but the
voter pipeline plus quorum threshold still makes the full-blended case
effectively infeasible under both models (see §5.3 "Full-blended worst
case").

---

## 10. Artifact Index

| File                                       | Description                                |
|--------------------------------------------|--------------------------------------------|
| `analysis.py`                              | Main Python analysis script (dual-model)   |
| `timing_derivation.md`                     | Derivation of the per-tx timing constants  |
| `pi1_derivation.md`                        | Empirical derivation of π₁ from mempool measurements |
| `analysis_log.md`                          | Log of critical junctures during analysis  |
| `plots/network_model_comparison.svg`       | Loss-rate sensitivity, Mathis vs CUBIC (§5.4) |
| `plots/pi1_sensitivity.svg`                | TxCache miss-rate sensitivity (§5.5)       |
| `plots/<model>/compare_models.svg`         | Existing vs. improved model CDF comparison |
| `plots/<model>/eb_closure_sweep.svg`       | CDF sweep over S_EB_tx values              |
| `plots/<model>/feasibility.svg`            | Liveness × safety vs. S_EB_tx (two views)  |
| `plots/<model>/certification.svg`          | Certification probability and quantiles    |
| `plots/<model>/outcome_diagram.svg`        | Schematic outcome diagram (fixed RB structure) |
| `plots/<model>/sensitivity_1hop_vs_blended.svg` | 1-hop vs. multi-hop closure fetch     |
| `plots/<model>/network_diffusion.svg`      | Network-only diffusion feasibility         |
| `results_summary_mathis.json`              | Numerical results under Mathis             |
| `results_summary_cubic.json`               | Numerical results under CUBIC              |

`<model>` is `mathis` or `cubic`.

**References for the throughput models:**
- Mathis et al. (1997), "The macroscopic behavior of the TCP congestion
  avoidance algorithm", ACM SIGCOMM CCR.
- Ha, Rhee, Xu (2008), "CUBIC: A new TCP-friendly high-speed TCP variant",
  ACM SIGOPS Operating Systems Review.  RFC 8312 standardises the
  Linux-kernel default.

---

## 11. References

- CIP-0164 – Ouroboros Leios
- `analysis/deltaq/linear-leios/docs/report.md` – Prior ΔQ analysis
- `post-cip/apply-reapply/ReadMe.md` – Ledger apply/reapply timing measurements
- `docs/deltaq_PraosModel.pdf` – Praos ΔQ analysis
- `docs/deltaq_complexity_management_strategy.pdf` – Backend complexity discussion
- `docs/Praos Performance Model.pdf` – Praos performance model (p_interrupted derivation)
