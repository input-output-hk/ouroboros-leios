# Leios closure diffusion after certification: numerical report

## Summary

This report estimates the probability that **all honest nodes have received and
processed an endorser block's (EB's) transaction closure, given that the EB
certifies**. It extends the
[conditional-certification analysis](../analysis/deltaq/improved-leios/conditional_certification_diffusion.md)
with **125 kB, 260 kB, and 500 kB closures**, alongside 1–12 MB closures.
Results are model estimates, including CPU processing, rather than measurements.

The **260 kB case is Musashi's configured transaction-closure limit**.  At
that size, the honest all-node p99 completion time is **3.30 s under both
network models**.  The committee selects the **900 highest-stake
pools**, matching the current implementation and Musashi's seat-count parameter.
Every table and plot uses **50% one-hop and 50% two-hop paths**
for missing-batch fetches, and
**EB body size = closure size × 40/260**.
At 260 kB, the body is 40 kB and p99.9 is **3.31 s under both models**.
The stationary missing fraction is **one sixth at every node**; it is not
a one-sixth probability that a node needs to fetch anything.

- **At the 14-second deadline**, closures up to 4 MB round to **100.0000%**
  all-node completion under both network models.  For larger closures, Mathis
  rounds to **0.0000%**, while CUBIC rounds to **100.0000%**, conditional on
  certification.
  Rounded 100% does not mean zero failure probability.
- **Smaller closures finish earlier.** Reducing the closure from 4 MB to 0.5 MB
  reduces the all-node 99th-percentile completion time from **13.74 s to 4.98 s**
  under Mathis, and from **10.98 s to 4.98 s** under CUBIC.
- **Certification is effectively certain through 4 MB under both models.**
  CUBIC gives **99.9165%** certification at 8 MB, **2.6906%** at 12 MB, and
  **2.5004%** at 12.288 MB.  For Mathis closures of 8 MB and above,
  certification becomes an extremely rare event in the Normal approximation;
  the conditional results there should be treated as approximation-sensitive.
- **The original report's largest case is 12.288 decimal MB**, labelled there
  as “12 MB”.  This report retains that exact size as a separate comparison
  row, but applies the same multi-hop fetch assumption as every other row.

## 1. What the numbers mean

The **closure size** is the total size of referenced transactions, not the EB
body size and not the amount each node must fetch. With the assumed cache miss
rate of one sixth, a 500 kB closure requires fetching approximately **83.33 kB**
of missing transactions; the node still processes the whole closure.

Two different probabilities appear below:

- **Voter ready by 7 s:** one node has received the body, fetched its missing
  transactions, and completed the voter validation work by the voting deadline.
- **All ready by t, given C:** every honest node has received the body, fetched
  its missing transactions, and completed reapplication by time *t*, conditional
  on the certification event *C*. This is a strict **all-node** target, not an
  average node, a stake fraction, or 99% of nodes.

All times are measured from the model's EB diffusion origin. The checkpoints
are **7 s** (voting deadline), **10 s** (intermediate checkpoint), and **14 s**
(end of the diffusion window). A p99 time is the time by which the all-node
completion event has probability at least 99%, conditional on certification.
An early completion time does not mean that the certificate itself has already
been delivered to every node: certificate propagation is not a stage of this
closure-completion calculation.

### Fixed inputs

| Input | Value used |
|:---|:---|
| Node population | 2,500; all honest in the baseline |
| Committee | Deterministic top-stake selection of 900 pools; synthetic stake coverage approximately 98.844483% |
| Committee size / effective equal-weight votes | 900 / approximately 464 |
| Stake distribution | Synthetic power-law distribution in `analysis.py`; not an observed stake snapshot |
| Certification threshold | 75% of total active stake; approximately 75.88% of committee stake |
| Voting / diffusion deadline | 7 s / 14 s |
| Stationary missing transaction fraction | Every node fetches 1/6 of the closure (approximately 16.67%) |
| Missing-transaction fetch | 50% one hop, 50% two hops for the whole missing batch; see §3.1 |
| EB-body diffusion | Full blended one-to-five-hop distribution from `report.md` §4.2 |
| EB body | Fixed size for each closure: closure size × 40/260; 40 kB at a 260 kB closure |
| Average transaction size | 1,000 bytes |
| CPU means | Voter mixture: approximately 0.1428 ms/transaction; reapply: 0.070 ms/transaction |
| Network models | Mathis (Reno/AIMD) and CUBIC |
| Packet loss / interface cap | 0.0001 / 1 Gbit/s |
| Short / medium / long RTT | 12 / 69 / 268 ms |
| Numerical time grid | 10 ms, extending to 40 s |

The selection rule follows the ledger's
[`selectLeiosCommittee`](https://github.com/IntersectMBO/cardano-ledger/blob/leios-prototype/libs/cardano-ledger-core/src/Cardano/Ledger/State/LeiosCommittee.hs):
take the configured number of pools in descending active-stake order, or all
candidates if fewer; equal-stake ties use ascending pool ID.  The synthetic
model carries no pool IDs, so equal-stake ties are interchangeable.  Coverage
is an outcome of selection, not a 99% target.  All selected seats are assumed
to have usable voting keys; the implementation can retain keyless seats when
keys are missing, expired, or have invalid proofs of possession.

The [pinned Musashi genesis](../testnet/config/dijkstra-genesis.json) sets
`leiosCommitteeSize=900`, `maxEndorserBlockTxsSize=260000`, and the separate
references-size limit to 40,000 bytes.  The 260 kB closure limit is a maximum,
not a measured average; transaction supply, packing, and execution limits can
produce smaller closures.  Its missing-transaction fetch is approximately
43.33 kB under the assumed one-sixth miss rate.  This remains an isolated-EB,
2,500-node model with the timing and network inputs above, rather than a full
calibration to Musashi's population, stake snapshot, or period lengths.

The same body-to-closure ratio applies to every size, without a cap.  For
example, a 4 MB closure has a 615.385 kB body and a 12 MB closure has a
1,846.15 kB body.  This is a modelling rule, not a measured encoding ratio;
larger rows extrapolate beyond Musashi's 40 kB references-size limit and
should not be interpreted as valid Musashi configurations.

**Units:** throughout this report, kB = 1,000 bytes and MB = 1,000,000 bytes.
The original note passes 1,024, 4,096, and 12,288 model kB for its “1, 4,
and 12 MB” rows. Those correspond to **1.024, 4.096, and 12.288 decimal MB**;
the 1, 4, and 12 MB rows below therefore use slightly different inputs.

## 2. Certification and completion probabilities

Very small certification probabilities are displayed in scientific notation
as percentages, rather than rounded to zero.
All certification probabilities in this sweep are numerically representable,
including the extremely small Mathis tails; every closure has a plotted curve.

The baseline has no adversarial nodes. All probabilities are percentages,
rounded to four decimal places. Thus `0.0000%` and `100.0000%` are rounded
values, not claims of impossibility or certainty. Smaller closures saturate
the 14-second column; §3 gives their more informative completion-time differences.

### Mathis: Reno/AIMD network model

| Closure (MB) | Body (kB) | Missing txs (kB) | Voter ready by 7 s | P(C) | All ready by 7 s, given C | All ready by 10 s, given C | All ready by 14 s, given C |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 0.125 | 19.2308 | 20.8333 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 0.26 | 40 | 43.3333 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 0.5 | 76.9231 | 83.3333 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 1 | 153.846 | 166.667 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 2 | 307.692 | 333.333 | 99.5994% | 100.0000% | 0.0122% | 100.0000% | 100.0000% |
| 4 | 615.385 | 666.667 | 86.7248% | 100.0000% | 0.0000% | 0.0002% | 100.0000% |
| 8 | 1230.77 | 1333.33 | 42.6110% | 6.4035e-46% | 0.0000% | 0.0000% | 0.0000% |
| 12 | 1846.15 | 2000 | 15.2651% | 4.4109e-287% | 0.0000% | 0.0000% | 0.0000% |
| 12.288 | 1890.46 | 2048 | 14.9895% | 4.6512e-294% | 0.0000% | 0.0000% | 0.0000% |

### CUBIC network model

| Closure (MB) | Body (kB) | Missing txs (kB) | Voter ready by 7 s | P(C) | All ready by 7 s, given C | All ready by 10 s, given C | All ready by 14 s, given C |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 0.125 | 19.2308 | 20.8333 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 0.26 | 40 | 43.3333 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 0.5 | 76.9231 | 83.3333 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 1 | 153.846 | 166.667 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 2 | 307.692 | 333.333 | 99.9261% | 100.0000% | 18.6229% | 100.0000% | 100.0000% |
| 4 | 615.385 | 666.667 | 96.0654% | 100.0000% | 0.0000% | 98.4236% | 100.0000% |
| 8 | 1230.77 | 1333.33 | 81.5363% | 99.9165% | 0.0000% | 0.0453% | 100.0000% |
| 12 | 1846.15 | 2000 | 71.8524% | 2.6906% | 0.0000% | 0.0000% | 100.0000% |
| 12.288 | 1890.46 | 2048 | 71.7836% | 2.5004% | 0.0000% | 0.0000% | 100.0000% |

A high individual voter readiness probability does not imply that every node
is ready.  For example, at 2 MB under Mathis, individual voter readiness at
7 s is **99.5994%**, while all-node reapplication completion is **0.0122%**.
Certification only requires the stake quorum, so it remains effectively certain.

### Conditional completion CDFs

All plots and tables use the **50% one-hop / 50% two-hop fetch distribution**
defined in §3.1.

Each curve shows the probability that all 2,500 honest nodes are ready by
time *t*, given certification, for one closure size. Vertical dotted lines
mark the 7, 10, and 14 s table checkpoints. The dashed size curve retains
the original report's 12.288 MB comparison case. Colours identify the same
closure sizes in all four CDF plots.

![Mathis conditional all-node closure completion CDFs for closures from 0.125 to 12.288 MB](conditional-certification-diffusion/mathis-honest-cdf.svg)

![CUBIC conditional all-node closure completion CDFs for closures from 0.125 to 12.288 MB](conditional-certification-diffusion/cubic-honest-cdf.svg)

## 3. Completion times and active-adversary comparison

The honest columns target all **2,500** nodes. The active-adversary columns
use the original note's scenario: an adversary controls **25% of committee
stake** and always votes on time, independently of honest diffusion. The model
also reduces the honest node target to **1,875**, assuming the same adversarial
fraction by node count. A stake fraction alone does not imply that node count.

Where certification is effectively certain, the slightly
earlier active p99 values mainly reflect the smaller completion target;
they are not evidence that adversarial voting improves diffusion. Comparisons
of the informational strength of certificates require holding the honest
population fixed.

### Mathis

| Closure (MB) | Honest p50 (s) | Honest p95 (s) | Honest p99 (s) | Honest p99.9 (s) | Active p99 (s) | Active all ready by 14 s, given C |
|---:|---:|---:|---:|---:|---:|---:|
| 0.125 | 1.73 | 1.80 | 2.01 | 2.02 | 2.01 | 100.0000% |
| 0.26 | 2.84 | 2.96 | 3.30 | 3.31 | 3.30 | 100.0000% |
| 0.5 | 4.28 | 4.46 | 4.98 | 4.99 | 4.97 | 100.0000% |
| 1 | 5.66 | 5.89 | 6.57 | 6.59 | 6.57 | 100.0000% |
| 2 | 8.11 | 8.44 | 9.41 | 9.43 | 9.40 | 100.0000% |
| 4 | 11.85 | 12.34 | 13.74 | 13.77 | 13.73 | 100.0000% |
| 8 | 16.44 | 18.53 | 18.59 | 18.60 | 18.63 | 0.0000% |
| 12 | 22.68 | 22.69 | 22.69 | 22.69 | 22.71 | 0.0000% |
| 12.288 | 23.14 | 23.15 | 23.15 | 23.15 | 23.17 | 0.0000% |

### CUBIC

| Closure (MB) | Honest p50 (s) | Honest p95 (s) | Honest p99 (s) | Honest p99.9 (s) | Active p99 (s) | Active all ready by 14 s, given C |
|---:|---:|---:|---:|---:|---:|---:|
| 0.125 | 1.73 | 1.80 | 2.01 | 2.02 | 2.01 | 100.0000% |
| 0.26 | 2.84 | 2.96 | 3.30 | 3.31 | 3.30 | 100.0000% |
| 0.5 | 4.28 | 4.46 | 4.98 | 4.99 | 4.97 | 100.0000% |
| 1 | 5.66 | 5.89 | 6.57 | 6.59 | 6.57 | 100.0000% |
| 2 | 7.75 | 8.07 | 9.00 | 9.02 | 8.99 | 100.0000% |
| 4 | 9.47 | 9.86 | 10.98 | 11.01 | 10.97 | 100.0000% |
| 8 | 11.37 | 11.83 | 13.15 | 13.19 | 13.13 | 100.0000% |
| 12 | 12.63 | 13.10 | 13.13 | 13.14 | 14.55 | 98.9861% |
| 12.288 | 12.77 | 13.24 | 13.27 | 13.28 | 14.71 | 98.9948% |

At 0.5 MB, the honest p99 time leaves **9.02 s** before the 14-second
deadline under both models.  At 4 MB, Mathis retains **0.26 s** and CUBIC
retains **3.02 s**.  These are model timing margins, not measured
budgets for additional traffic or implementation overhead.

### Completion-time percentiles by closure size

The percentile plot uses a logarithmic closure-size axis to keep the smaller
sizes legible. Each panel includes the honest p50, p95, p99, and p99.9 times,
with the active-adversary p99 shown as a dashed black line. The rightmost
points include both 12 and 12.288 MB under both network models.
Where certification saturates, the
active line nearly overlaps honest p99 because the main difference is the
smaller honest-node target.  The rare-certification rows also have different
quorum-conditioning factors; their rare-event approximation can put active
p99 later than honest p99.

![Conditional all-node completion-time percentiles versus closure size for Mathis and CUBIC](conditional-certification-diffusion/completion-time-percentiles.svg)

### Active-adversary conditional completion CDFs

These use the same axes and size colours as the honest-baseline plots, but
target all 1,875 honest nodes under the 25% active-adversary scenario.
Both honest and active-adversary plots use the fixed fetch mixture.

![Mathis conditional closure completion CDFs with 25% active adversarial committee stake and 1,875 honest nodes](conditional-certification-diffusion/mathis-active-cdf.svg)

![CUBIC conditional closure completion CDFs with 25% active adversarial committee stake and 1,875 honest nodes](conditional-certification-diffusion/cubic-active-cdf.svg)

### 3.1. Fixed missing-transaction fetch model

Every result uses the same fetch model for the **whole missing-transaction
batch**: **50% one hop and 50% two hops**.  These weights are modelling
assumptions, not measured mainnet frequencies:

| Path length | Probability |
|---:|---:|
| 1 hop | 50% |
| 2 hops | 50% |

The generator sets `DEFAULT_HOP_WEIGHTS=(0.5, 0.5)` for missing batches only.
EB bodies retain the full blended one-to-five-hop distribution from
[`report.md` §4.2](../analysis/deltaq/improved-leios/report.md#42-network-model),
implemented by `cdf_blended_delay` using `analysis.py`'s `_HOP_PROBS`.
Two-hop fetching represents data being acquired upstream before it reaches
the requesting node.  Each hop transfers the same missing batch using the existing
short/medium/long-distance transfer law, independently of the other hops;
hop CDFs are convolved sequentially without pipelining.  The EB-body diffusion
and CPU laws are unchanged.

The **stationary transaction-cache miss fraction is 1/6 at every node**.
Each node therefore fetches a batch of size `closure / 6`, with the path
length drawn from the equal one/two-hop mixture.  There is no additional 5/6
probability of a full-closure cache hit.  This is a mean-fraction approximation:
it does not sample which individual transactions are missing or model them
taking different paths.  The model also omits peer-discovery delays,
timeouts, retries, and contention.

Only the missing fraction traverses these fetch paths; this is not the
§5.3 catastrophic pre-diffusion-failure scenario in `report.md`, in which the
entire closure must traverse the network.

## 4. Interpretation and scope

For the smaller sizes, **earlier readiness and timing margin** distinguish the
options more usefully than the rounded 14-second probability.  Reducing a
500 kB closure to 125 kB also reduces the body from approximately 76.92 kB
to 19.23 kB, reducing p99 by **2.97 s under both models**.  These rows model
jointly smaller bodies and closures, rather than isolating closure-fetch costs.

The following assumptions bound what these figures establish:

- **One EB in isolation.** Concurrent EBs, transaction traffic, and resource
  contention are not modelled. These tables do not determine sustainable
  throughput or a production closure-size limit.
- **Independent, stake-independent node completion times.** Shared network
  paths, correlated cache misses, and differences in SPO connectivity are not
  represented; no general direction of error is established here.
- **Two CPU laws.** The implementation uses full voter validation for
  certification and reapply-only processing for the all-node diffusion term.
  Combining these in the conditional formula is a first-order approximation,
  not the exact single-law derivation in the original note.  Where certification
  saturates, results numerically agree with the reapply-only all-node power
  term.  When certification does not saturate, including the largest CUBIC
  rows and the rare-certification Mathis rows, the conditioning factor matters;
  mixing laws and enforcing monotonicity can produce sharp steps and unstable
  tail percentiles.  Those conditional figures are not reliable predictions
  of operational rare-event behaviour.
- **Approximate quorum tails.** Certification uses a Normal approximation to
  a stake-weighted vote sum. In the original note's silent-adversary case,
   25% withholding leaves at most approximately 74.13% of total active stake
   with the current 900-seat synthetic committee, below the
  75% threshold: certification is impossible. The Normal approximation can
  nevertheless return a positive tail. No conditional completion probability
  is defined for that impossible event, so it is not tabulated here.
- **Discrete numerical model.** Transfer-time steps, fixed mixtures, and the
  10 ms grid produce plateaus and sharp tail changes.  For example, the
  Mathis 14-second result changes from **100.0000% at 4 MB** to
  a value rounding to **0.0000% at 8 MB**, while certification also becomes rare.
  This is a model result, not a measured
  operational cliff; displayed precision supports reproducibility rather
  than equivalent predictive accuracy.

## 5. Reproducing the tables and plots

The tables and plots use the existing
[`analysis.py`](../analysis/deltaq/improved-leios/analysis.py) implementation,
with `include_validation=True` and the fixed inputs above. The
[report generator](../analysis/deltaq/improved-leios/closure_diffusion.py)
prints four tables, writes five SVG plots to
`docs/conditional-certification-diffusion/`, and checks that the computed CDFs are bounded and
non-decreasing, that certification probabilities are non-negative and bounded,
and that conditional curves agree numerically with the reapply-only all-node
curves when certification saturates.  Both voter and reapplication calculations
use the same closure-scaled body size and fixed fetch-hop mixture.

From the repository root, in a Python environment with NumPy, SciPy, and
Matplotlib installed:

```sh
python3 analysis/deltaq/improved-leios/closure_diffusion.py
```

For the mathematical derivation and broader discussion, see the
[original note](../analysis/deltaq/improved-leios/conditional_certification_diffusion.md);
for the component network and CPU models, see the
[full analysis report](../analysis/deltaq/improved-leios/report.md).
