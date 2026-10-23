# Leios closure diffusion after certification: numerical report

## Summary

This report estimates the probability that **all honest nodes have received and
processed an endorser block's (EB's) transaction closure, given that the EB
certifies**. It extends the
[conditional-certification analysis](../analysis/deltaq/improved-leios/conditional_certification_diffusion.md)
with **125 kB, 260 kB, and 500 kB closures**, alongside 1–12 MB closures.
Results are model estimates, including CPU processing, rather than measurements.

The **260 kB case is Musashi's configured transaction-closure limit**.  At
that size, the honest all-node p99 completion time is **4.01 s under both
network models**.  The committee selects the **900 highest-stake
pools**, matching the current implementation and Musashi's seat-count parameter.
Every table and plot uses a **causal two-phase model**: blended fetching and
validation before the 7-second deadline, then **50% one-hop / 50% two-hop
recovery for nodes still missing data** on certification, with
**EB body size = closure size × 40/260**.
At 260 kB, the body is 40 kB and p99.9 is **4.36 s under both models**.
The stationary missing fraction is **one sixth at every node**; it is not
a one-sixth probability that a node needs to fetch anything.

- **At the 14-second deadline**, closures up to 4 MB round to **100.0000%**
  all-node completion under both network models, with effectively certain
  certification through 2 MB.  At 8 MB, Mathis rounds to **0.0000%** all-node
  completion by 14 s, while CUBIC rounds to **100.0000%**, conditional on
  certification.  Rounded 100% does not mean zero failure probability.
- **Smaller closures finish earlier.** Reducing the closure from 4 MB to 0.5 MB
  reduces the all-node 99th-percentile completion time from **13.76 s to 5.98 s**
  under Mathis and from **11.00 s to 5.98 s** under CUBIC.
- **Certification is effectively certain through 2 MB under both models.**
  CUBIC gives **99.6413%** certification at 4 MB.  For Mathis closures of
  4 MB and above, and CUBIC closures of 8 MB and above,
  certification becomes extremely rare.  Quorum probabilities use a seeded
  permutation estimate, not a Normal tail; extreme-tail values remain
  sensitive to the finite permutation sample and synthetic stake distribution.

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
| Phase-one missing-transaction fetch | Full blended one-to-five-hop distribution; determines voter readiness and P(C) |
| Phase-two recovery | Begins no earlier than 7 s, conditional on certification: 50% one hop, 50% two hops; see §3.1 |
| EB-body diffusion | Full blended one-to-five-hop distribution from `report.md` §4.2 |
| EB body | Fixed size for each closure: closure size × 40/260; 40 kB at a 260 kB closure |
| Average transaction size | 1,000 bytes |
| CPU means | Initial validation: approximately 0.1428 ms/transaction; recovery reapply: 0.070 ms/transaction |
| Quorum calculation | 50,000 seeded pool permutations (seed 164); binomial mixture evaluated in log space |
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
Certification and conditional probabilities are evaluated in log space; even
the extremely small Mathis tails remain numerically representable as logs.
Every closure size has a plotted curve.  Scientific notation does not imply
that such extreme tails are empirically calibrated.

The baseline has no adversarial nodes. All probabilities are percentages,
rounded to four decimal places. Thus `0.0000%` and `100.0000%` are rounded
values, not claims of impossibility or certainty. Smaller closures saturate
the 14-second column; §3 gives their more informative completion-time differences.

### Mathis: Reno/AIMD network model

| Closure (MB) | Body (kB) | Missing txs (kB) | Voter ready by 7 s | P(C) | All ready by 7 s, given C | All ready by 10 s, given C | All ready by 14 s, given C |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 0.125 | 19.2308 | 20.8333 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 0.26 | 40 | 43.3333 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 0.5 | 76.9231 | 83.3333 | 100.0000% | 100.0000% | 99.9967% | 100.0000% | 100.0000% |
| 1 | 153.846 | 166.667 | 99.9800% | 100.0000% | 60.5871% | 100.0000% | 100.0000% |
| 2 | 307.692 | 333.333 | 93.5955% | 100.0000% | 0.0000% | 100.0000% | 100.0000% |
| 4 | 615.385 | 666.667 | 55.1347% | 6.4872e-23% | 0.0000% | 0.0000% | 100.0000% |
| 8 | 1230.77 | 1333.33 | 16.6900% | 1.7273e-278% | 0.0000% | 0.0000% | 0.0000% |
| 12 | 1846.15 | 2000 | 4.6231% | 1.6401e-614% | 0.0000% | 0.0000% | 0.0000% |

### CUBIC network model

| Closure (MB) | Body (kB) | Missing txs (kB) | Voter ready by 7 s | P(C) | All ready by 7 s, given C | All ready by 10 s, given C | All ready by 14 s, given C |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 0.125 | 19.2308 | 20.8333 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 0.26 | 40 | 43.3333 | 100.0000% | 100.0000% | 100.0000% | 100.0000% | 100.0000% |
| 0.5 | 76.9231 | 83.3333 | 100.0000% | 100.0000% | 99.9967% | 100.0000% | 100.0000% |
| 1 | 153.846 | 166.667 | 99.9800% | 100.0000% | 60.5871% | 100.0000% | 100.0000% |
| 2 | 307.692 | 333.333 | 94.9502% | 100.0000% | 0.0000% | 100.0000% | 100.0000% |
| 4 | 615.385 | 666.667 | 80.9318% | 99.6413% | 0.0000% | 0.0000% | 100.0000% |
| 8 | 1230.77 | 1333.33 | 54.3077% | 5.9575e-25% | 0.0000% | 0.0000% | 100.0000% |
| 12 | 1846.15 | 2000 | 36.9762% | 5.2942e-93% | 0.0000% | 0.0000% | 98.7205% |

A high individual voter readiness probability does not imply that every node
is ready.  For example, at 2 MB under Mathis, individual voter readiness at
7 s is **93.5955%**, while all-node completion rounds to **0.0000%**.
Certification only requires the stake quorum, so it remains effectively certain.

### Conditional completion CDFs

All plots and tables use the **two-phase node process** defined
in §3.1; the 50% one-hop / 50% two-hop assumption does not enter P(C).

Each curve shows the probability that all 2,500 honest nodes are ready by
time *t*, given certification, for one closure size. Vertical dotted lines
mark the 7, 10, and 14 s table checkpoints.  Colours identify the same
closure sizes in all four CDF plots.

![Mathis conditional all-node closure completion CDFs for closures from 0.125 to 12 MB](conditional-certification-diffusion/mathis-honest-cdf.svg)

![CUBIC conditional all-node closure completion CDFs for closures from 0.125 to 12 MB](conditional-certification-diffusion/cubic-honest-cdf.svg)

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
| 0.125 | 2.16 | 2.40 | 2.45 | 2.67 | 2.45 | 100.0000% |
| 0.26 | 3.53 | 3.92 | 4.01 | 4.36 | 4.01 | 100.0000% |
| 0.5 | 5.27 | 5.83 | 5.98 | 6.50 | 5.98 | 100.0000% |
| 1 | 6.98 | 8.27 | 8.99 | 9.00 | 8.98 | 100.0000% |
| 2 | 9.89 | 9.90 | 9.91 | 9.92 | 9.91 | 100.0000% |
| 4 | 11.86 | 12.35 | 13.76 | 13.79 | 13.74 | 100.0000% |
| 8 | 18.48 | 19.23 | 21.38 | 21.44 | 19.28 | 0.0000% |
| 12 | 25.71 | 26.75 | 29.75 | 29.82 | 26.82 | 0.0000% |

### CUBIC

| Closure (MB) | Honest p50 (s) | Honest p95 (s) | Honest p99 (s) | Honest p99.9 (s) | Active p99 (s) | Active all ready by 14 s, given C |
|---:|---:|---:|---:|---:|---:|---:|
| 0.125 | 2.16 | 2.40 | 2.45 | 2.67 | 2.45 | 100.0000% |
| 0.26 | 3.53 | 3.92 | 4.01 | 4.36 | 4.01 | 100.0000% |
| 0.5 | 5.27 | 5.83 | 5.98 | 6.50 | 5.98 | 100.0000% |
| 1 | 6.98 | 8.27 | 8.99 | 9.00 | 8.98 | 100.0000% |
| 2 | 9.73 | 9.74 | 9.75 | 9.76 | 9.75 | 100.0000% |
| 4 | 10.43 | 10.44 | 11.00 | 11.03 | 10.99 | 100.0000% |
| 8 | 11.38 | 11.85 | 13.16 | 13.21 | 13.14 | 100.0000% |
| 12 | 12.64 | 13.14 | 14.57 | 14.64 | 13.22 | 99.0257% |

At 0.5 MB, the honest p99 time leaves **8.02 s** before the 14-second
deadline under both models.  At 4 MB, conditional p99 leaves **0.24 s under
Mathis** and **3.00 s under CUBIC**; the Mathis certificate itself is extremely
unlikely.  These are model timing margins, not measured
budgets for additional traffic or implementation overhead.

### Completion-time percentiles by closure size

The percentile plot uses a logarithmic closure-size axis to keep the smaller
sizes legible. Each panel includes the honest p50, p95, p99, and p99.9 times,
with the active-adversary p99 shown as a dashed black line.  The rightmost
point is 12 MB under both models.
Where certification saturates, the
active line nearly overlaps honest p99 because the main difference is the
smaller honest-node target.  Conditioning on rare certification also changes
the distribution of nodes already ready at the deadline.  The new calculation
does not impose monotonicity by taking a running maximum of the CDF.

![Conditional all-node completion-time percentiles versus closure size for Mathis and CUBIC](conditional-certification-diffusion/completion-time-percentiles.svg)

### Active-adversary conditional completion CDFs

These use the same axes and size colours as the honest-baseline plots, but
target all 1,875 honest nodes under the 25% active-adversary scenario.
Both honest and active-adversary plots use the split fetch assumptions.

![Mathis conditional closure completion CDFs with 25% active adversarial committee stake and 1,875 honest nodes](conditional-certification-diffusion/mathis-active-cdf.svg)

![CUBIC conditional closure completion CDFs with 25% active adversarial committee stake and 1,875 honest nodes](conditional-certification-diffusion/cubic-active-cdf.svg)

### 3.1. Fixed missing-transaction fetch model

The model uses separate paths for the **whole missing-transaction batch**
before and after the voting deadline:

| Path length | Phase-one fetch | Phase-two recovery |
|---:|---:|---:|
| 1 hop | 0.40% | 50% |
| 2 hops | 3.91% | 50% |
| 3 hops | 31.06% | 0% |
| 4 hops | 61.85% | 0% |
| 5 hops | 2.78% | 0% |

**Phase one:** every honest node attempts to acquire and validate the closure.
Voter readiness and the unconditional certification probability P(C) use only
the full blended fetch law and initial validation.  Nodes outside the committee
also follow this initial processing law, but do not vote.

**Phase two starts at 7 s, conditional on certification.**  A node already
validated remains complete.  A node that has fetched its entire missing batch
continues any validation still in progress.  A node still missing data uses
the short-path recovery law, beginning at the later of 7 s and its body arrival,
then reapplies the closure.  Already completed data fetching is retained;
partial bytes of an unfinished batch are not credited, so that batch is
restarted in full.  This is a deliberately coarse batch-level progress model.

Certified holders are assumed to be immediately available as serving sources
at the deadline.  There is no additional certificate-construction, delivery,
source-discovery, or queueing delay.  Recovery does not happen on a branch
where certification fails.  This is a fixed-deadline model, not a model of
the earliest possible quorum time or per-node certificate arrival.

The generator sets `DEFAULT_HOP_WEIGHTS=(0.5, 0.5)` for recovery only.  These
weights are modelling assumptions, not measured mainnet frequencies.
EB bodies retain the full blended distribution from
[`report.md` §4.2](../analysis/deltaq/improved-leios/report.md#42-network-model),
implemented by `cdf_blended_delay` using `analysis.py`'s `_HOP_PROBS`.
Two-hop fetching represents data being acquired upstream before it reaches
the requesting node.  Each hop transfers the same missing batch using the existing
short/medium/long-distance transfer law, independently of the other hops;
hop CDFs are convolved sequentially without pipelining.  The EB-body diffusion
and CPU laws are unchanged.

The **stationary transaction-cache miss fraction is 1/6 at every node**.
Each node therefore fetches a batch of size `closure / 6`, with the path
length drawn from the applicable phase's distribution.  There is no additional 5/6
probability of a full-closure cache hit.  This is a mean-fraction approximation:
it does not sample which individual transactions are missing or model them
taking different paths.  The model also omits peer-discovery delays,
timeouts, retries, and contention.

Only the missing fraction traverses these fetch paths; this is not the
§5.3 catastrophic pre-diffusion-failure scenario in `report.md`, in which the
entire closure must traverse the network.

### 3.2. Joint readiness and conditional completion

Let *B* be body arrival, *U* the phase-one missing-batch fetch duration,
*X* initial validation, *R* recovery duration, and *Y* reapplication.  Component
durations are independent; both phases share the same body arrival.  Set
*L = B + U*, *V = L + X*, and define completion *D* on a certified branch by:

$$
D = \begin{cases}
V, & L \le t_v,\\
\max(B,t_v)+R+Y, & L > t_v,
\end{cases}
\qquad t_v=7\ \mathrm{s}.
$$

Thus a node ready to vote is necessarily already complete.  For independent
node histories, the required joint probability is known explicitly:

$$
H(t_v,t)=P(V\le t_v,D\le t)=F_V(\min(t_v,t)).
$$

Writing *A_t* for all honest nodes completing by *t*, the conditional CDF is:

$$
P(A_t\mid C)=F_D(t)^{N_h}
\frac{Q\!\left(H(t_v,t)/F_D(t)\right)}{Q(F_V(t_v))}.
$$

This uses the actual conditional voter probability *H/F_D*, rather than the
old substitution involving *F_V(t_v)/F_V(t)*.  The denominator and phase-one
vote readiness do not change when the recovery-hop distribution changes.
The identity is exact under the independent-node model with an exact *Q*;
the report approximates *Q* using the reproducible method below.

### 3.3. Stake-weighted quorum calculation

For a committee of *K* seats, let *a_k* be the probability that a uniformly
chosen subset of *k* seats carries quorum stake.  Then:

$$
Q(p)=\sum_{k=0}^{K} a_k {K\choose k}p^k(1-p)^{K-k}.
$$

The implementation estimates all *a_k* using **50,000 uniform random pool
permutations**, with **seed 164**.  For each permutation it records the first
prefix whose stake reaches quorum; the empirical CDF of this prefix length
estimates *a_k*.  The same coefficients are used for the denominator and
conditional numerator.  This is not rejection sampling of rare certification
events, and the binomial mixture is evaluated in log space.

The non-negative mixture preserves a consistent probability model: the
conditional curves are bounded and non-decreasing without clipping excursions
or taking a running maximum.  Roundoff at unity is trimmed only within a
small numerical tolerance.  The quorum calculation is still a finite-sample
approximation to the exact stake-weighted distribution; very rare tails can
depend strongly on favourable subsets absent from the sample.

For the stylised active-adversary comparison, 25% of committee weight votes
deterministically and each stochastic seat's weight is scaled by 75%.
This does not identify an actual allocation of adversarial pools; the honest
completion target remains 1,875 nodes, following the earlier comparison.

## 4. Interpretation and scope

For the smaller sizes, **earlier readiness and timing margin** distinguish the
options more usefully than the rounded 14-second probability.  Reducing a
500 kB closure to 125 kB also reduces the body from approximately 76.92 kB
to 19.23 kB, reducing p99 by **3.53 s under both models**.  These rows model
jointly smaller bodies and closures, rather than isolating closure-fetch costs.

The following assumptions bound what these figures establish:

- **One EB in isolation.** Concurrent EBs, transaction traffic, and resource
  contention are not modelled. These tables do not determine sustainable
  throughput or a production closure-size limit.
- **Independent, stake-independent node completion times.** Shared network
  paths, correlated cache misses, and differences in SPO connectivity are not
  represented; no general direction of error is established here.
- **Idealised recovery boundary.** Immediate serving availability at 7 s and
  independent, uncontended recovery are assumptions.  Restarting unfinished
  missing batches ignores partial-byte progress.  Real certificate arrival,
  fetching overlap, and shared serving capacity can alter the result.
- **Approximate quorum coefficients.** The permutation estimate preserves
  probability identities but is not an exact enumeration of all subsets.
  Decimal precision is for reproducibility, not confidence in extremely rare
  probabilities.  A silent adversary withholding 25% of committee stake would
  leave approximately 74.13% of active stake, below quorum; such an impossible
  event has no conditional completion distribution and is not tabulated.
- **Discrete numerical model.** Transfer-time steps, fixed mixtures, and the
  10 ms grid produce plateaus and sharp tail changes.  For example, the
  recovery onset and deterministic transfer mixtures can create plateaus and
  sharp jumps.  Sums in the two-phase module place two positive grid durations
  at their summed time, correcting the earlier convolution's one-bin advance
  per composition.  This also shifts some voter-readiness figures slightly.

## 5. Reproducing the tables and plots

The tables and plots use the component laws in
[`analysis.py`](../analysis/deltaq/improved-leios/analysis.py), combined by the
causal process and quorum calculation in
[`two_phase.py`](../analysis/deltaq/improved-leios/two_phase.py), with the fixed
inputs above.  The older mixed-readiness approximation in `analysis.py` is no
longer used by this report.  The
[report generator](../analysis/deltaq/improved-leios/closure_diffusion.py)
prints four tables, writes five SVG plots to
`docs/conditional-certification-diffusion/`, and checks that the computed CDFs are bounded and
non-decreasing, that certification probabilities are non-negative and bounded,
and that conditional curves agree numerically with the two-phase node CDF
raised to the population count when certification saturates.  CDF monotonicity
is checked without repair.

From the repository root, in a Python environment with NumPy, SciPy, and
Matplotlib installed:

```sh
python3 analysis/deltaq/improved-leios/closure_diffusion.py
```

The targeted tests cover phase timing, retained validation, late bodies,
recovery independence of certification, small exact conditional examples,
quorum-coefficient estimation, and log-space underflow handling:

```sh
python3 -m unittest discover -s analysis/deltaq/improved-leios -p test_two_phase.py
```

For the mathematical derivation and broader discussion, see the
[original note](../analysis/deltaq/improved-leios/conditional_certification_diffusion.md);
for the component network and CPU models, see the
[full analysis report](../analysis/deltaq/improved-leios/report.md).
