# Compute (CPU) cost estimation per node

> [!Note]
> This analysis assumes fully utilized block space for a conservative upper bound
> on costs. All timing values are derived from the CIP simulation configuration
> (`analysis/sims/cip/experiments/config.yaml`), which contains benchmark
> measurements for protocol operations sourced from `db-analyser` runs on
> Cardano mainnet and cryptography prototype benchmarks.

## Ouroboros Praos

We start with Ouroboros Praos to establish a baseline. In Praos, CPU utilization
comes from block header validation and block body application.

| Component                      | Validation Time      | Source                              |
| ------------------------------ | -------------------- | ----------------------------------- |
| Block header validation        | 0.4438 ms            | `rb-head-validation-cpu-time-ms`; `db-analyser` empty-block baseline |
| Block body constant            | 0.3539 ms            | `rb-body-legacy-praos-payload-validation-cpu-time-ms-constant`; `Reapply` linear model |
| Block body per byte            | 0.00002151 ms/B      | `rb-body-legacy-praos-payload-validation-cpu-time-ms-per-byte`; `Reapply` linear model |

### Block Rate Calculation

| Parameter               | Value    | Formula            |
| ----------------------- | -------- | ------------------ |
| Slot length             | 1 second | Protocol parameter |
| Active slot coefficient | 0.05     | Protocol parameter |
| **Blocks per second**   | **0.05** | $$1 \times 0.05$$  |

### Praos CPU Calculation (0.05 blocks/s)

$$C_{\text{praos}} = 0.05 \times \bigl(0.4438 + (0.3539 + 90{,}112 \times 0.00002151)\bigr)$$

$$C_{\text{praos}} = 0.05 \times (0.4438 + 2.293) \approx 0.137\text{ ms/s}$$

Thus, Praos at 0.05 blocks/s consumes approximately 0.14 ms of CPU time per
second — about 0.014% of a single CPU core. This is the baseline for comparison.

> [!Note]
> The body validation uses the empirical `Reapply` model from `db-analyser`
> measurements (`docs/technical-report-2.md`). The old default config used a
> 50 ms constant for body validation, which was a rough placeholder rather than
> a measured value.

## Ouroboros Leios

In Linear Leios (CIP-164), CPU utilization comes from five components:
full transaction validation (`Apply`), ledger re-application (`Reapply`),
EB header validation, vote validation, and certificate validation.

### Apply vs. Reapply

Transactions in Leios are gossiped via the mempool and referenced by hash in
EBs. CPU is consumed in two distinct ways:

- **Apply (full validation)**: Performed when a transaction first arrives at a
  node (mempool ingestion). Includes signature verification and Plutus script
  evaluation (if present). Cost: **0.6201 ms/tx** (constant; from linear model
  of `db-analyser` mainnet data for the `Apply` operation without explicit
  Plutus term; see `docs/technical-report-2.md`).

- **Reapply (ledger application)**: Performed when a certified EB is applied
  to the ledger state. Assumes the transactions were already validated; skips
  signature and script re-verification. Cost: **0.3539 ms constant + 0.00002151
  ms/B** per certified EB (from `Reapply` linear model).

For this cost estimate we apply the `Apply` cost conservatively to all nodes
for every confirmed transaction. In practice, a relay that receives an EB
before its individual transactions (under `eb-received` propagation) only pays
the cheaper `Reapply` cost; the `Apply` cost is the upper bound.

Plutus script execution is not modeled here; it adds up to ~1 ms per Giga-step
on top of the `Apply` baseline (see `docs/technical-report-2.md`).

### Component Processing Times

| Component                    | Cost                      | Config Reference                                  |
| ---------------------------- | ------------------------- | ------------------------------------------------- |
| Transaction Apply (full)     | 0.6201 ms/tx              | `tx-validation-cpu-time-ms`                       |
| Transaction Reapply (ledger) | 0.3539 ms + 0.00002151 ms/B | `eb-body-validation-cpu-time-ms-*`              |
| EB header validation         | 0.4438 ms/EB              | `eb-header-validation-cpu-time-ms`                |
| Vote validation              | 2.9 ms/vote               | `vote-validation-cpu-time-ms`; non-persistent worst case |
| Certificate validation       | 157.2 ms/cert             | `cert-validation-cpu-time-ms-constant`            |

### Base Parameters

| Parameter             | Value           | Source                                          |
| --------------------- | --------------- | ----------------------------------------------- |
| EB rate               | 0.05 EB/s       | Active slot coefficient                         |
| Votes per EB          | 600             | `vote-generation-probability`; wFA+LS committee |
| P(EB certified)       | ≈ 0.48          | Poisson: P(next RB ≥ 14 slots away): vote (4) + diffuse (7) + diffusion margin (3) |
| Certified EBs/s       | 0.024           | $0.05 \times 0.48$                              |
| Average tx size       | 1,500 bytes     | Conservative estimate                           |

### CPU Usage Formulas

1. **Transaction Apply CPU** (scales with confirmed throughput):

   $$C_{\text{apply}} = \frac{\text{TxkB/s} \times 1{,}000}{S_{\text{tx}}} \times t_{\text{apply}}$$

   where $S_{\text{tx}} = 1{,}500$ bytes and $t_{\text{apply}} = 0.6201$ ms/tx.

2. **Transaction Reapply CPU** (per certified EB, scales with throughput):

   $$C_{\text{reapply}} = N_{\text{cert}} \times \left(0.3539 + 0.00002151 \times \frac{\text{TxkB/s} \times 1{,}000}{N_{\text{cert}}}\right)$$

   Simplifying (where $N_{\text{cert}} = 0.024$ cert/s):

   $$C_{\text{reapply}} = 0.0085 + 0.02151 \times \text{TxkB/s} \text{ ms/s}$$

3. **EB Header Validation CPU** (fixed):

   $$C_{\text{eb}} = 0.05 \times 0.4438 = 0.022\text{ ms/s}$$

4. **Vote Validation CPU** (fixed — dominant at low throughput):

   $$C_{\text{vote}} = 600 \times 0.05 \times 2.9 = 87.0\text{ ms/s}$$

5. **Certificate Validation CPU** (fixed):

   $$C_{\text{cert}} = 0.024 \times 157.2 = 3.77\text{ ms/s}$$

6. **Total CPU**:

   $$C_{\text{total}} = C_{\text{apply}} + C_{\text{reapply}} + C_{\text{eb}} + C_{\text{vote}} + C_{\text{cert}}$$

### CPU Calculation at 4.5 TxkB/s (Praos-equivalent throughput)

1. **Tx Apply**: $\frac{4{,}500}{1{,}500} \times 0.6201 = 3 \times 0.6201 = 1.860\text{ ms/s}$

2. **Tx Reapply**: $0.0085 + 0.02151 \times 4.5 = 0.105\text{ ms/s}$

3. **EB Header**: $0.022\text{ ms/s}$

4. **Vote Validation**: $87.0\text{ ms/s}$

5. **Certificate Validation**: $3.77\text{ ms/s}$

6. **Total**:
   $$C_{\text{total}} = 1.860 + 0.105 + 0.022 + 87.0 + 3.77 = 92.76\text{ ms/s} \approx 9.3\%\text{ of one core}$$

At Praos-equivalent throughput, vote processing dominates (93.8% of CPU) due to
the fixed cost of validating 600 votes per EB regardless of transaction volume.

### CPU Utilization at Different Confirmed Throughputs

| TxkB/s | Tx/s | Tx Apply | Tx Reapply | EB Hdr | Vote   | Cert   | Total ms/s | % of One Core | Rec. Cores |
| ------ | ---- | -------- | ---------- | ------ | ------ | ------ | ---------- | ------------- | ---------- |
| 4.5    | 3    | 1.86ms   | 0.11ms     | 0.02ms | 87.0ms | 3.77ms | 92.76ms    | 9.3%          | 2          |
| 50     | 33   | 20.67ms  | 1.08ms     | 0.02ms | 87.0ms | 3.77ms | 112.54ms   | 11.3%         | 2          |
| 100    | 67   | 41.34ms  | 2.16ms     | 0.02ms | 87.0ms | 3.77ms | 134.29ms   | 13.4%         | 2          |
| 150    | 100  | 62.01ms  | 3.24ms     | 0.02ms | 87.0ms | 3.77ms | 156.04ms   | 15.6%         | 2          |
| 200    | 133  | 82.68ms  | 4.31ms     | 0.02ms | 87.0ms | 3.77ms | 177.78ms   | 17.8%         | 2          |
| 250    | 167  | 103.35ms | 5.39ms     | 0.02ms | 87.0ms | 3.77ms | 199.53ms   | 20.0%         | 2          |
| 300    | 200  | 124.02ms | 6.46ms     | 0.02ms | 87.0ms | 3.77ms | 221.27ms   | 22.1%         | 2          |

> [!Note]
>
> - Tx/s assumes average transaction size of 1,500 bytes
> - "% of One Core" = Total ms/s ÷ 1,000ms
> - "Rec. Cores" is 2 for all levels based on the CPU math; 4 cores recommended
>   for production to cover GHC GC pressure, OS/network overhead, and burst load
> - Tx Apply uses the upper-bound Apply cost for all nodes; relays that receive
>   EBs before individual txs only pay the cheaper Reapply cost
> - Plutus script execution adds ~1 ms/Gstep on top of the Apply baseline;
>   not modeled here as it depends on workload composition

### CPU Component Analysis (at 200 TxkB/s)

| Component              | CPU Time  | % of Total |
| ---------------------- | --------- | ---------- |
| Vote Validation        | 87.0ms    | 48.9%      |
| Tx Apply (full)        | 82.68ms   | 46.5%      |
| Tx Reapply (ledger)    | 4.31ms    | 2.4%       |
| Certificate Validation | 3.77ms    | 2.1%       |
| EB Header Validation   | 0.022ms   | < 0.1%     |

At 200 TxkB/s, vote validation (48.9%) and transaction Apply (46.5%) are
roughly equal contributors. The fixed vote overhead of 87 ms/s is always
present regardless of throughput.

### Comparative Efficiency (Leios vs. Praos)

| TxkB/s | Leios CPU (ms/s) | CPU per TxkB/s (ms) | Praos CPU per TxkB/s (ms) | Leios:Praos ratio |
| ------ | ---------------- | ------------------- | ------------------------- | ----------------- |
| 4.5    | 92.76ms          | 20.6                | 0.030                     | 685:1             |
| 50     | 112.54ms         | 2.25                | 0.030 (would not scale)   | 75:1              |
| 100    | 134.29ms         | 1.34                | —                         | 44:1              |
| 200    | 177.78ms         | 0.89                | —                         | 29:1              |
| 300    | 221.27ms         | 0.74                | —                         | 24:1              |

The high Leios:Praos ratios at all throughput levels are dominated by the fixed
vote overhead (87 ms/s), compared to Praos' very small measured baseline
(0.137 ms/s from `db-analyser`). At 300 TxkB/s, Leios delivers 67× more
confirmed throughput than Praos while using ~24× more CPU.

## Monthly Cost by Cloud Provider ($)

Using standard compute-optimized instances. 2 cores satisfies the CPU
requirement at all modeled throughput levels; 4 cores recommended for
production deployments.

| Provider   | 2 Core  | 4 Core  | Notes                  |
| ---------- | ------- | ------- | ---------------------- |
| AWS c6i    | $62.05  | $124.10 | On-demand, US East     |
| GCP c2/n2  | $52.34  | $152.35 | On-demand, US Central1 |
| Azure Fsv2 | $61.76  | $123.37 | On-demand, East US     |
| DO CPU-Opt | $42.00  | $84.00  | Regular pricing        |
| Linode     | $36.00  | $60.00  | Standard pricing       |
| Hetzner    | $6.59   | $17.80  | EUR prices at 1 EUR = 1.10 USD |

> [!Note]
>
> - Prices are for US regions and may vary by location
> - Assumes dedicated compute-optimized instances
> - Does not include potential savings from reserved instances or spot pricing

## Recommendations

1. **CPU floor**: 2 cores covers all throughput levels up to 300 TxkB/s
   (peak 22% of one core)
2. **Production**: 4 cores recommended to handle GHC GC, UTxO-HD I/O waits,
   Plutus script workloads, and burst conditions — consistent with the CIP-164
   hardware recommendation
3. **Above 300 TxkB/s**: Additional cores needed for transaction Apply
   parallelism

> [!Important]
>
> Real-world performance may require more cores due to:
>
> - GHC garbage collector pressure (especially during protocol burst attacks)
> - Disk I/O wait for UTxO-HD ledger state access
> - Uneven workload distribution across stages
> - Plutus script execution (~1 ms/Gstep, not modeled here)
> - Other node operations not included in calculation

## Compute Cost Sources

| Provider     | Instance Type | Source                                                               | Last Updated |
| ------------ | ------------- | -------------------------------------------------------------------- | ------------ |
| AWS          | c6i           | https://aws.amazon.com/ec2/pricing/on-demand/                        | Apr 2025     |
| GCP          | c2/n2         | https://cloud.google.com/compute/vm-instance-pricing                 | Apr 2025     |
| Azure        | Fsv2          | https://azure.microsoft.com/pricing/details/virtual-machines/series/ | Apr 2025     |
| DigitalOcean | CPU-Optimized | https://www.digitalocean.com/pricing/compute                         | Apr 2025     |
| Linode       | Dedicated CPU | https://www.linode.com/pricing/                                      | Apr 2025     |
| Hetzner      | CPX11         | https://www.hetzner.com/cloud/pricing                                | Apr 2026     |
