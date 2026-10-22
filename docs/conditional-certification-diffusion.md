# Leios closure diffusion after certification: numerical report

## Summary

This report estimates the probability that **all honest nodes have received and
processed an endorser block's (EB's) transaction closure, given that the EB
certifies**. It extends the
[conditional-certification analysis](../analysis/deltaq/improved-leios/conditional_certification_diffusion.md)
with **125 kB, 250 kB, 260 kB, and 500 kB closures**, alongside 1–12 MB closures.
Results are model estimates, including CPU processing, rather than measurements.

The **260 kB case is Musashi's configured transaction-closure limit**.  At
that size, the honest all-node p99 completion time is **8.74 s under Mathis**
and **7.39 s under CUBIC**.  The committee selects the **900 highest-stake
pools**, matching the current implementation and Musashi's seat-count parameter.

- **At the 14-second deadline**, every closure from 0.125 to 12 decimal MB
  reaches all 2,500 honest nodes with a probability that rounds to **100.0000%**
  under both network models. Rounded 100% does not mean zero failure probability.
- **Smaller closures finish earlier.** Reducing the closure from 4 MB to 0.5 MB
  reduces the all-node 99th-percentile completion time from **9.67 s to 8.77 s**
  under Mathis, and from **8.10 s to 7.42 s** under CUBIC.
- **Certification is effectively certain throughout this sweep.** Consequently,
  conditioning on certification adds negligible information at these parameters;
  the results primarily describe the model's diffusion and reapplication tail.
- **The original report's largest case is 12.288 decimal MB**, labelled there
  as “12 MB”. At that exact size, Mathis gives **99.9009%** all-node completion
  by 14 s, reproducing its approximately 0.9990 result. This report retains that
  case as a separate comparison row.

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
| Missing transaction fraction | 1/6 (approximately 16.67%) |
| Missing-transaction fetch | One hop from the peer forwarding the EB body |
| EB body | Equal-weight mixture of 1, 64, 256, and 512 kB; unchanged across closure sizes |
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

**Units:** throughout this report, kB = 1,000 bytes and MB = 1,000,000 bytes.
The original note passes 1,024, 4,096, and 12,288 model kB for its “1, 4,
and 12 MB” rows. Those correspond to **1.024, 4.096, and 12.288 decimal MB**;
the 1, 4, and 12 MB rows below therefore use slightly different inputs.

## 2. Certification and completion probabilities

The baseline has no adversarial nodes. All probabilities are percentages,
rounded to four decimal places. Thus `0.0000%` and `100.0000%` are rounded
values, not claims of impossibility or certainty. Smaller closures saturate
the 14-second column; §3 gives their more informative completion-time differences.

### Mathis: Reno/AIMD network model

| Closure (MB) | Missing txs (kB) | Voter ready by 7 s | P(C) | All ready by 7 s, given C | All ready by 10 s, given C | All ready by 14 s, given C |
|---:|---:|---:|---:|---:|---:|---:|
| 0.125 | 20.8333 | 99.9473% | 100.0000% | 26.7902% | 100.0000% | 100.0000% |
| 0.25 | 41.6667 | 99.9007% | 100.0000% | 24.9030% | 100.0000% | 100.0000% |
| 0.26 | 43.3333 | 99.8871% | 100.0000% | 24.5005% | 100.0000% | 100.0000% |
| 0.5 | 83.3333 | 99.7777% | 100.0000% | 9.2920% | 100.0000% | 100.0000% |
| 1 | 166.667 | 99.7759% | 100.0000% | 0.3668% | 100.0000% | 100.0000% |
| 2 | 333.333 | 99.7293% | 100.0000% | 0.1169% | 99.6036% | 100.0000% |
| 4 | 666.667 | 99.6538% | 100.0000% | 0.0184% | 99.6036% | 100.0000% |
| 8 | 1333.33 | 98.8228% | 100.0000% | 0.0000% | 73.1398% | 100.0000% |
| 12 | 2000 | 95.3621% | 100.0000% | 0.0000% | 4.6013% | 100.0000% |
| 12.288 | 2048 | 94.8242% | 100.0000% | 0.0000% | 3.5366% | 99.9009% |

### CUBIC network model

| Closure (MB) | Missing txs (kB) | Voter ready by 7 s | P(C) | All ready by 7 s, given C | All ready by 10 s, given C | All ready by 14 s, given C |
|---:|---:|---:|---:|---:|---:|---:|
| 0.125 | 20.8333 | 99.9971% | 100.0000% | 93.0993% | 100.0000% | 100.0000% |
| 0.25 | 41.6667 | 99.9971% | 100.0000% | 93.0993% | 100.0000% | 100.0000% |
| 0.26 | 43.3333 | 99.9971% | 100.0000% | 93.0993% | 100.0000% | 100.0000% |
| 0.5 | 83.3333 | 99.9963% | 100.0000% | 91.2787% | 100.0000% | 100.0000% |
| 1 | 166.667 | 99.9953% | 100.0000% | 90.9096% | 100.0000% | 100.0000% |
| 2 | 333.333 | 99.9848% | 100.0000% | 68.3616% | 100.0000% | 100.0000% |
| 4 | 666.667 | 99.9812% | 100.0000% | 67.0166% | 100.0000% | 100.0000% |
| 8 | 1333.33 | 99.6910% | 100.0000% | 15.0907% | 100.0000% | 100.0000% |
| 12 | 2000 | 99.2707% | 100.0000% | 1.7731% | 99.6036% | 100.0000% |
| 12.288 | 2048 | 99.2403% | 100.0000% | 1.7667% | 99.6036% | 100.0000% |

A high individual voter readiness probability does not imply that every node
is ready. For example, at 0.5 MB under Mathis, individual voter readiness at
7 s is **99.7777%**, while all-node reapplication completion is **9.2920%**.
Certification only requires the stake quorum, so it remains effectively certain.

### Conditional completion CDFs

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

Certification remains effectively certain in this scenario. The slightly
earlier active p99 values mainly reflect the smaller completion target;
they are not evidence that adversarial voting improves diffusion. Comparisons
of the informational strength of certificates require holding the honest
population fixed.

### Mathis

| Closure (MB) | Honest p50 (s) | Honest p95 (s) | Honest p99 (s) | Honest p99.9 (s) | Active p99 (s) | Active all ready by 14 s, given C |
|---:|---:|---:|---:|---:|---:|---:|
| 0.125 | 7.27 | 8.71 | 8.72 | 9.02 | 8.72 | 100.0000% |
| 0.25 | 7.42 | 8.72 | 8.74 | 9.21 | 8.73 | 100.0000% |
| 0.26 | 7.42 | 8.72 | 8.74 | 9.22 | 8.73 | 100.0000% |
| 0.5 | 7.43 | 8.74 | 8.77 | 9.46 | 8.75 | 100.0000% |
| 1 | 7.46 | 8.77 | 8.81 | 9.73 | 8.79 | 100.0000% |
| 2 | 7.54 | 8.85 | 8.92 | 10.21 | 8.91 | 100.0000% |
| 4 | 7.94 | 9.26 | 9.67 | 10.98 | 9.67 | 100.0000% |
| 8 | 9.35 | 10.68 | 11.09 | 12.39 | 11.08 | 100.0000% |
| 12 | 10.85 | 12.18 | 12.59 | 13.89 | 12.58 | 100.0000% |
| 12.288 | 10.97 | 12.29 | 12.70 | 14.00 | 12.69 | 99.9256% |

### CUBIC

| Closure (MB) | Honest p50 (s) | Honest p95 (s) | Honest p99 (s) | Honest p99.9 (s) | Active p99 (s) | Active all ready by 14 s, given C |
|---:|---:|---:|---:|---:|---:|---:|
| 0.125 | 6.19 | 7.36 | 7.37 | 7.67 | 7.37 | 100.0000% |
| 0.25 | 6.28 | 7.37 | 7.39 | 7.86 | 7.38 | 100.0000% |
| 0.26 | 6.28 | 7.37 | 7.39 | 7.87 | 7.38 | 100.0000% |
| 0.5 | 6.29 | 7.39 | 7.42 | 8.11 | 7.40 | 100.0000% |
| 1 | 6.32 | 7.42 | 7.46 | 8.38 | 7.44 | 100.0000% |
| 2 | 6.40 | 7.50 | 7.70 | 8.78 | 7.69 | 100.0000% |
| 4 | 6.65 | 7.76 | 8.10 | 9.20 | 8.10 | 100.0000% |
| 8 | 7.21 | 8.31 | 8.66 | 9.75 | 8.65 | 100.0000% |
| 12 | 7.66 | 8.77 | 9.11 | 10.20 | 9.10 | 100.0000% |
| 12.288 | 7.70 | 8.81 | 9.15 | 10.24 | 9.14 | 100.0000% |

At 0.5 MB, the honest p99 time leaves **5.23 s** before the 14-second
deadline under Mathis and **6.58 s** under CUBIC. At 4 MB those margins
are **4.33 s** and **5.90 s**. These are model timing margins, not measured
budgets for additional traffic or implementation overhead.

### Completion-time percentiles by closure size

The percentile plot uses a logarithmic closure-size axis to keep the smaller
sizes legible. Each panel includes the honest p50, p95, p99, and p99.9 times,
with the active-adversary p99 shown as a dashed black line. The rightmost
points include both 12 and 12.288 MB. The active line nearly overlaps honest
p99 because certification saturates and the main difference is the smaller
honest-node target.

![Conditional all-node completion-time percentiles versus closure size for Mathis and CUBIC](conditional-certification-diffusion/completion-time-percentiles.svg)

### Active-adversary conditional completion CDFs

These use the same axes and size colours as the honest-baseline plots, but
target all 1,875 honest nodes under the 25% active-adversary scenario.

![Mathis conditional closure completion CDFs with 25% active adversarial committee stake and 1,875 honest nodes](conditional-certification-diffusion/mathis-active-cdf.svg)

![CUBIC conditional closure completion CDFs with 25% active adversarial committee stake and 1,875 honest nodes](conditional-certification-diffusion/cubic-active-cdf.svg)

## 4. Interpretation and scope

For the smaller sizes, **earlier readiness and timing margin** distinguish the
options more usefully than the rounded 14-second probability. There is also
a substantial fixed diffusion cost: reducing a 500 kB closure to 125 kB only
reduces p99 by **0.05 s** under either network model. The EB-body distribution
is held fixed even for small closures, so these rows isolate closure-size
effects rather than model a jointly smaller body and closure.

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
  not the exact single-law derivation in the original note. In this sweep the
  quorum factor is effectively one, and the results numerically agree with
  the reapply-only all-node power term.
- **Approximate quorum tails.** Certification uses a Normal approximation to
  a stake-weighted vote sum. In the original note's silent-adversary case,
   25% withholding leaves at most approximately 74.13% of total active stake
   with the current 900-seat synthetic committee, below the
  75% threshold: certification is impossible. The Normal approximation can
  nevertheless return a positive tail. No conditional completion probability
  is defined for that impossible event, so it is not tabulated here.
- **Discrete numerical model.** Transfer-time steps, fixed mixtures, and the
  10 ms grid produce plateaus and sharp tail changes. For example, the
  Mathis 14-second result changes from **99.9999985% at 12 MB** to
  **99.9008545% at 12.288 MB**. This is a model result, not a measured
  operational cliff; displayed precision supports reproducibility rather
  than equivalent predictive accuracy.

## 5. Reproducing the tables and plots

The tables and plots use the existing
[`analysis.py`](../analysis/deltaq/improved-leios/analysis.py) implementation,
with `include_validation=True` and the fixed inputs above. The
[report generator](../analysis/deltaq/improved-leios/tsc_closure_diffusion.py)
prints all four tables, writes the five SVG plots to
`docs/conditional-certification-diffusion/`, and checks that the computed CDFs are bounded and
non-decreasing, that baseline certification saturates, and that the baseline
conditional curves agree numerically with the reapply-only all-node curves.

From the repository root, in a Python environment with NumPy, SciPy, and
Matplotlib installed:

```sh
python3 analysis/deltaq/improved-leios/tsc_closure_diffusion.py
```

For the mathematical derivation and broader discussion, see the
[original note](../analysis/deltaq/improved-leios/conditional_certification_diffusion.md);
for the component network and CPU models, see the
[full analysis report](../analysis/deltaq/improved-leios/report.md).
