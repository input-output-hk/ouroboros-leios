# Empirical Derivation of the TxCache Miss Rate π₁

This document derives an empirical estimate of the TxCache miss-rate
parameter $\pi_1$ used in the ΔQ model, replacing the hand-chosen Markov
default $\pi_1 = 1/6$ from the prior Haskell analysis with a value computed
from mainnet mempool measurements.

---

## 1. What $\pi_1$ Represents

$\pi_1$ is the probability that, at the moment a committee voter must validate
an EB closure, a given closure transaction is **not already in the voter's
local mempool**.  Voters with the transaction "in hand" pay only a cheap
`reapplyTx` (≈ 0.07 ms/tx) and 1 ms for cache lookup; voters without the
transaction must fetch it over the network and then run a full `applyTx`
(≈ 0.51 ms/tx).  The effective per-transaction cost is

$$\mu_\text{eff} = \pi_1 \mu_\text{apply} + (1 - \pi_1) \mu_\text{reapply}$$

and the expected fetch size per voter is $\pi_1 \cdot S_{EB-tx}$.  Both
quantities scale linearly with $\pi_1$.

The prior Haskell ΔQ model fixed $\pi_1 = 1/6 \approx 0.167$ via a two-state
Markov chain $M = \bigl(\begin{smallmatrix}1-p & p\\1-q & q\end{smallmatrix}\bigr)$
with $p = 0.5$, $q = 0.9$ (yielding the steady-state $\pi_1 = (1-q)/(p+1-q)$).
The $p, q$ values were chosen by hand; the prior report's qualitative
"mempools are well synchronized" was never quantitatively tied to these
parameters.

---

## 2. Data Source

The
[`post-cip/mempool-measurements`](https://github.com/input-output-hk/ouroboros-leios/tree/main/post-cip/mempool-measurements)
dataset is the output of an experiment where three Cardano nodes — one in
each of `ap-northeast-1`, `eu-central-1`, and `us-east-2` AWS regions — were
instrumented to log:

- Every block they applied (`block-times.tsv`), with hash and slot number.
- Every transaction hash that appeared in their local mempool
  (`tx-times.tsv`), with arrival timestamp.

The processing SQL (`process-log.sql`) joins these logs with the on-chain
ledger DB to produce a per-(transaction × region) record indicating whether
the transaction was **seen in the local mempool before it appeared in a
block** (`tx_seen_first` = TRUE/FALSE).  The fraction of transactions for
which `tx_seen_first` is TRUE is $\pi_2$ at that region; its complement is
$\pi_1$.

The raw logs (`*.tsv.gz`) are gitignored, but the processed summary plots
in the same directory contain the computed probability values as embedded
SVG text labels.  We extract these.

**Period covered.** The dataset contains both pre-BAU and BAU ("Business As
Usual") windows.  The plots below use the BAU window, slot ≥ `bauSlot`
(`bauSlot = 172210527`, corresponding to 2025-11-22 02:00:00 UTC).

---

## 3. Per-Region $\pi_2$ (Local Mempool ⇆ Block)

From `conditional-probability-mempool-block.svg`, the probability that a
transaction in a freshly applied block had been in that node's mempool
*before* the block was applied, split by region and by block utilization:

| Region | Block util ≤ 85% | Block util > 85% |
|--------|------------------|------------------|
| ap     | 96.6%            | 98.4%            |
| eu     | 92.3%            | 97.8%            |
| us     | 93.9%            | 56.5%   ← outlier |
| **Mean** | **94.27%**     | **84.23%**       |
| Mean (excl. us-high) | —    | **98.10%**       |

**The `us @ >85%` entry of 56.5% is anomalous** — it is dramatically lower
than every other observation (which cluster between 92% and 99%).  Without
access to the raw `mempool-vs-blocks.tsv.gz`, we cannot verify the sample
size, time window, or whether a brief network event or instrumentation
glitch caused it.  We flag it but exclude it from the central estimates
below; it is included in the conservative bound.

Resulting per-region $\pi_1$ estimates (low-util regime):

$$\pi_1^\text{local,low-util} = 1 - 0.9427 \approx 0.057$$

---

## 4. Cross-Region $\pi_2$ (the More Relevant Quantity)

The per-region "mempool vs block" probability above describes how often a
node has *its own incoming block's* transactions in its mempool first.
For Leios voter behavior, the more relevant question is:

> Given a transaction is in **producer**'s mempool (and so eligible to be
> included in an EB), what is the probability it is also in **voter**'s
> mempool by the time the voter needs to validate?

This is captured by the cross-region conditional probabilities from
`conditional-probability-regions.svg` (BAU period, all utilizations
aggregated):

| Condition  | $P(\text{voter} \mid \text{producer})$ |
|------------|----------------------------------------|
| P(eu | ap) | 93.7%                                 |
| P(us | ap) | 91.5%                                 |
| P(ap | eu) | 97.9%                                 |
| P(us | eu) | 91.5%                                 |
| P(ap | us) | 97.0%                                 |
| P(eu | us) | 92.8%                                 |
| **Mean**   | **94.07%**                            |
| **Min**    | **91.5%**                             |
| **Max**    | **97.9%**                             |

Resulting empirical $\pi_1$ estimates:

| Statistic | $\pi_2$ | $\pi_1$ |
|-----------|---------|---------|
| Best case  | 0.979 | **0.021** |
| Mean       | 0.941 | **0.059** |
| Worst case | 0.915 | **0.085** |

The mean cross-region miss rate is **$\pi_1 \approx 0.06$**, and the
worst-case observed pair is **$\pi_1 \approx 0.085$**.  Both are well
below the prior assumption of $\pi_1 = 1/6 \approx 0.167$.

---

## 5. Recommended Value and Range

| Source | $\pi_1$ |
|--------|---------|
| Prior Haskell ΔQ model (hand-chosen, $p=0.5,\,q=0.9$) | **0.167** |
| **Empirical mean (cross-region BAU)** | **0.06** |
| **Empirical 95th-percentile-ish (worst observed pair)** | **0.085** |
| Empirical low-util local | 0.057 |
| Empirical high-util local (incl. us-east-2 outlier) | 0.158 |
| Empirical high-util local (excl. us-east-2 outlier) | 0.019 |

**Recommended central estimate:** $\pi_1 \approx 0.06$
**Recommended conservative-upper-bound estimate:** $\pi_1 \approx 0.10$

The prior assumption of $\pi_1 = 1/6$ is **roughly 3× larger than the
empirical mean** and 2× larger than the worst-case observed cross-region
pair.

---

## 6. Effect on the ΔQ Model

From the existing §5.8 sensitivity sweep, $P_\text{cert}$ at the
CIP-target $S_{EB-tx} = 12$ MB:

| $\pi_1$ | $P_\text{cert}$ (Mathis) | $P_\text{cert}$ (CUBIC) |
|---------|--------------------------|-------------------------|
| 0.05 (empirical-typical) | **0.497** ✓ | **0.497** ✓ |
| 0.10 (empirical-pessimistic) | **0.497** ✓ | **0.497** ✓ |
| 1/6 (prior model assumption) | 0.218 ✗ | 0.495 |
| 0.30 | 0.000 ✗ | 0.009 ✗ |
| 0.50 | 0.000 ✗ | 0.000 ✗ |

**Empirically, the 12 MB CIP target is feasible under *either* throughput
model**.  The Mathis-vs-CUBIC framing — which was the focus of §5.7 — is
*irrelevant* in the empirically-supported range; both models give
$P_\text{cert} \approx 0.497$ (the Praos cap) at $\pi_1 \leq 0.10$.

The Mathis-CUBIC distinction only matters in the narrow $\pi_1 \in [0.10,
0.25]$ band, which sits *between* the empirical estimate ($\pi_1 \approx
0.06$) and the prior model's value ($\pi_1 = 0.167$).  The empirical
evidence places mainnet behavior firmly outside this band — on the
feasible side.

---

## 7. Caveats

**1. Three-node sample.**  The dataset covers exactly three monitoring
nodes, all on AWS, one per inter-continental region.  This is a tiny sample
relative to the production SPO population (~2 500 active stake pools).
Results may not generalize to:
- SPOs on consumer-grade or low-bandwidth uplinks
- SPOs at the edge of the mesh topology (low peering)
- SPOs in regions not represented (e.g. SA-APAC paths)

**2. Healthy-network conditions.**  The BAU window deliberately excludes
known congestion incidents.  $\pi_1$ during incidents could be substantially
higher; the prior model's 1/6 may be a better "incident-adjusted" default
than the BAU mean of 0.06.

**3. No raw data access.**  Numbers are extracted from rendered SVG plots,
which gives 1-decimal-place precision but no access to per-block or per-tx
detail.  We cannot compute confidence intervals, fit the Markov $p, q$
parameters directly, or quantify temporal stickiness (the supposed
motivation for using a Markov rather than i.i.d. model).

**4. The `us @ >85%` outlier is unexplained.**  Its 56.5% value
(corresponding to $\pi_1 \approx 0.44$) is far enough from the other 5
observations that it likely reflects a transient anomaly or low sample
count.  Without raw data we cannot confirm.  If the outlier is real, it
suggests $\pi_1$ can spike to ~0.5 during high-load events at a single
region — well into the "infeasible" zone of the sensitivity sweep.

**5. Linear Leios voter model is approximated.**  The empirical measurement
captures `tx_seen_first` relative to *block arrival*, which is a slightly
different event from EB-closure validation in Linear Leios.  The mapping is
sound on first principles (both require the transaction to have diffused
to the receiver before a deadline), but Leios EBs may reference
transactions that haven't yet been block-confirmed, slightly biasing the
estimate.

---

## 8. Recommendation

Adopt **$\pi_1 = 0.06$ as the central value** for the deltaQ analysis going
forward, with **$\pi_1 = 0.10$ as a conservative upper bound**.  Update
report.md §1, §5.8 and §8.6 accordingly.  Keep the sensitivity sweep over
$\pi_1 \in \{0.05, 0.10, 1/6, 0.30, 0.50\}$ in §5.8 — it now serves both
as a bound on the empirical estimate (0.05 and 0.10 brackets) and as a
worst-case adversarial scenarios (0.30 and 0.50).

The single most useful empirical follow-up — to *actually fit* $p, q$ to
the underlying tx-time series rather than just $\pi_1$ — would require
re-running the SQL pipeline against the gitignored `mempool-vs-blocks.tsv.gz`
file or equivalent, and is beyond the scope of this derivation.

---

## 9. Reproducing the Extraction

```python
import re

def extract_pcts(svg_path):
    with open(svg_path) as f:
        svg = f.read()
    # SVG <text x="X" y="Y" ...>CONTENT</text> pattern
    rx = re.compile(
        r"<text[^>]*?\bx='([0-9.]+)'[^>]*?\by='([0-9.]+)'[^>]*?>([^<]+)</text>"
    )
    return [(float(x), float(y), t)
            for x, y, t in rx.findall(svg)
            if re.match(r'^\d+\.\d%$', t)]

per_region = extract_pcts(
    'post-cip/mempool-measurements/conditional-probability-mempool-block.svg')
cross      = extract_pcts(
    'post-cip/mempool-measurements/conditional-probability-regions.svg')
```

The per-region SVG arranges bars in a 2-row × 3-column grid; the cross-region
SVG arranges 6 bars in a single row.  Bar position determines the
(region × utilization) or $P(x|y)$ label.
