# Compute (CPU) cost estimation per node

> [!Note]
> This analysis assumes fully utilized block space and **full Plutus execution
> unit utilization per transaction** (20 Gstep/tx) for a conservative upper
> bound on costs. Real-world workloads typically use far less than the maximum
> Plutus budget; actual CPU costs will be lower. All timing values are derived
> from the CIP simulation configuration
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
  evaluation. Cost: **19.594 ms/tx** = 0.6201 ms base + 0.9487 ms/Gstep ×
  20 Gstep/tx (max tx execution units, fully utilized upper bound). The
  0.9487 ms/Gstep Plutus coefficient is from OLS regression on `db-analyser`
  mainnet data; see `docs/technical-report-2.md`.

- **Reapply (ledger application)**: Performed when an EB's transactions are
  applied to the ledger state. Assumes the transactions were already validated;
  skips signature and Plutus re-execution. Cost: **0.3539 ms constant +
  0.00002151 ms/B** per EB (from `Reapply` linear model).

For this cost estimate we apply the `Apply` cost conservatively to all nodes
for every confirmed transaction. In practice, a relay that receives an EB
before its individual transactions (under `eb-received` propagation) only pays
the cheaper `Reapply` cost; the `Apply` cost is the upper bound.

### Component Processing Times

| Component                    | Cost                      | Config Reference                                  |
| ---------------------------- | ------------------------- | ------------------------------------------------- |
| Transaction Apply (full)     | 19.594 ms/tx              | `tx-validation-cpu-time-ms` + 0.9487 ms/Gstep × 20 Gstep/tx |
| Transaction Reapply (ledger) | 0.3539 ms + 0.00002151 ms/B | `eb-body-validation-cpu-time-ms-*`              |
| EB header validation         | 0.4438 ms/EB              | `eb-header-validation-cpu-time-ms`                |
| Vote validation              | 2.9 ms/vote               | `vote-validation-cpu-time-ms`; non-persistent worst case |
| Certificate validation       | 157.2 ms/cert             | `cert-validation-cpu-time-ms-constant`            |

### Base Parameters

| Parameter             | Value           | Source                                          |
| --------------------- | --------------- | ----------------------------------------------- |
| EB rate               | 0.05 EB/s       | Active slot coefficient                         |
| Votes per EB          | 600             | `vote-generation-probability`; wFA+LS committee |
| P(EB certified)       | ≈ 0.48          | Poisson: P(next RB ≥ 14 slots away); affects latency, not asymptotic throughput |
| Average tx size       | 1,500 bytes     | Conservative estimate                           |
| Tx exec unit limit    | 20 Gstep/tx     | Protocol parameter (tx execution unit budget)   |
| Plutus coefficient    | 0.9487 ms/Gstep | `db-analyser` OLS regression for `Apply`        |

### CPU Usage Formulas

1. **Transaction Apply CPU** (scales with confirmed throughput):

   $$C_{\text{apply}} = \frac{\text{TxkB/s} \times 1{,}000}{S_{\text{tx}}} \times t_{\text{apply}}$$

   where $S_{\text{tx}} = 1{,}500$ bytes and $t_{\text{apply}} = 0.6201 + 0.9487 \times 20 = 19.594$ ms/tx.

2. **Transaction Reapply CPU** (per EB, scales with throughput):

   $$C_{\text{reapply}} = R_{\text{eb}} \times \left(0.3539 + 0.00002151 \times \frac{\text{TxkB/s} \times 1{,}000}{R_{\text{eb}}}\right)$$

   Simplifying (where $R_{\text{eb}} = 0.05$ EB/s; P(cert) cancels in the dominant term):

   $$C_{\text{reapply}} = 0.0177 + 0.02151 \times \text{TxkB/s} \text{ ms/s}$$

3. **EB Header Validation CPU** (fixed):

   $$C_{\text{eb}} = 0.05 \times 0.4438 = 0.022\text{ ms/s}$$

4. **Vote Validation CPU** (fixed):

   $$C_{\text{vote}} = 600 \times 0.05 \times 2.9 = 87.0\text{ ms/s}$$

5. **Certificate Validation CPU** (fixed):

   $$C_{\text{cert}} = 0.05 \times 157.2 = 7.86\text{ ms/s}$$

6. **Total CPU**:

   $$C_{\text{total}} = C_{\text{apply}} + C_{\text{reapply}} + C_{\text{eb}} + C_{\text{vote}} + C_{\text{cert}}$$

### CPU Calculation at 4.5 TxkB/s (Praos-equivalent throughput)

1. **Tx Apply**: $\frac{4{,}500}{1{,}500} \times 19.594 = 3 \times 19.594 = 58.78\text{ ms/s}$

2. **Tx Reapply**: $0.0177 + 0.02151 \times 4.5 = 0.11\text{ ms/s}$

3. **EB Header**: $0.022\text{ ms/s}$

4. **Vote Validation**: $87.0\text{ ms/s}$

5. **Certificate Validation**: $7.86\text{ ms/s}$

6. **Total**:
   $$C_{\text{total}} = 58.78 + 0.11 + 0.022 + 87.0 + 7.86 = 153.8\text{ ms/s} \approx 15.4\%\text{ of one core}$$

At Praos-equivalent throughput, vote validation (56.6%) and transaction Apply
(38.2%) are the two dominant components.

### CPU Utilization at Different Confirmed Throughputs

| TxkB/s | Tx/s | Tx Apply   | Tx Reapply | EB Hdr | Vote   | Cert   | Total ms/s | % of One Core | Min Cores |
| ------ | ---- | ---------- | ---------- | ------ | ------ | ------ | ---------- | ------------- | --------- |
| 4.5    | 3    | 58.78ms    | 0.11ms     | 0.02ms | 87.0ms | 7.86ms | 153.8ms    | 15.4%         | 2         |
| 50     | 33   | 653.1ms    | 1.09ms     | 0.02ms | 87.0ms | 7.86ms | 749.1ms    | 74.9%         | 2         |
| 100    | 67   | 1,306.3ms  | 2.17ms     | 0.02ms | 87.0ms | 7.86ms | 1,403.4ms  | 140.3%        | 2         |
| 150    | 100  | 1,959.4ms  | 3.24ms     | 0.02ms | 87.0ms | 7.86ms | 2,057.5ms  | 205.8%        | 3         |
| 200    | 133  | 2,612.5ms  | 4.32ms     | 0.02ms | 87.0ms | 7.86ms | 2,711.7ms  | 271.2%        | 3         |
| 250    | 167  | 3,265.7ms  | 5.39ms     | 0.02ms | 87.0ms | 7.86ms | 3,366.0ms  | 336.6%        | 4         |
| 300    | 200  | 3,918.8ms  | 6.47ms     | 0.02ms | 87.0ms | 7.86ms | 4,020.2ms  | 402.0%        | 5         |

> [!Note]
>
> - Tx/s assumes average transaction size of 1,500 bytes
> - "% of One Core" = Total ms/s ÷ 1,000ms
> - "Min Cores" = minimum cores to run without overload; add at least 1–2 cores
>   of production headroom for GHC GC pressure, OS/network overhead, and burst
> - Tx Apply includes Plutus execution at the full 20 Gstep/tx limit
> - Tx Apply uses the upper-bound Apply cost; relays that receive EBs before
>   individual txs only pay the cheaper Reapply cost

### CPU Component Analysis (at 200 TxkB/s)

| Component              | CPU Time    | % of Total |
| ---------------------- | ----------- | ---------- |
| Tx Apply (full)        | 2,612.5ms   | 96.3%      |
| Vote Validation        | 87.0ms      | 3.2%       |
| Certificate Validation | 7.86ms      | 0.3%       |
| Tx Reapply (ledger)    | 4.32ms      | 0.2%       |
| EB Header Validation   | 0.022ms     | < 0.1%     |

At 200 TxkB/s, transaction Apply dominates (96.3%) due to Plutus execution
modeled at full tx execution unit utilization (20 Gstep/tx).

### Comparative Efficiency (Leios vs. Praos)

| TxkB/s | Leios CPU (ms/s) | CPU per TxkB/s (ms) | Praos CPU per TxkB/s (ms) | Leios:Praos ratio |
| ------ | ---------------- | ------------------- | ------------------------- | ----------------- |
| 4.5    | 153.8ms          | 34.2                | 0.030                     | 1,140:1           |
| 50     | 749.1ms          | 15.0                | 0.030 (would not scale)   | 500:1             |
| 100    | 1,403.4ms        | 14.0                | —                         | 467:1             |
| 200    | 2,711.7ms        | 13.6                | —                         | 453:1             |
| 300    | 4,020.2ms        | 13.4                | —                         | 447:1             |

The Leios:Praos ratios reflect the Plutus-dominated Apply cost and fixed vote
overhead, against Praos' very small measured baseline (0.137 ms/s). At 300
TxkB/s, Leios delivers 67× more confirmed throughput than Praos while using
~447× more CPU — driven by modeling Plutus at full execution unit utilization.

## Monthly Cost by Cloud Provider ($)

Using standard compute-optimized instances. Required core count varies by
throughput (see table above): 2 cores for ≤100 TxkB/s, 3–4 cores for
150–250 TxkB/s, 5+ cores at 300 TxkB/s.

| Provider   | 2 Core  | 4 Core  | Notes                          |
| ---------- | ------- | ------- | ------------------------------ |
| AWS c6i    | $62.05  | $124.10 | On-demand, US East             |
| GCP c2/n2  | $52.34  | $152.35 | On-demand, US Central1         |
| Azure Fsv2 | $61.76  | $123.37 | On-demand, East US             |
| DO CPU-Opt | $42.00  | $84.00  | Regular pricing                |
| Linode     | $36.00  | $60.00  | Standard pricing               |
| Hetzner    | $6.59   | $17.80  | EUR prices at 1 EUR = 1.10 USD |

> [!Note]
>
> - Prices are for US regions and may vary by location
> - Assumes dedicated compute-optimized instances
> - Does not include potential savings from reserved instances or spot pricing

## Recommendations

1. **≤100 TxkB/s**: 2 cores minimum (peak ~140% of one core); 4 cores for
   production headroom
2. **150–250 TxkB/s**: 4 cores minimum (up to ~337% of one core); 6 cores
   for production headroom
3. **300 TxkB/s**: 6 cores minimum (402% of one core); consistent with the
   CIP-164 hardware recommendation of 4+ cores at lower utilization
4. **Above 300 TxkB/s**: Additional cores needed; transaction Apply parallelism
   required

> [!Important]
>
> Real-world performance may require more cores due to:
>
> - GHC garbage collector pressure (especially during protocol burst attacks)
> - Disk I/O wait for UTxO-HD ledger state access
> - Uneven workload distribution across stages
> - Other node operations not included in calculation
> - Actual Plutus workloads vary; 20 Gstep/tx is the per-tx upper bound

## Compute Cost Sources

| Provider     | Instance Type | Source                                                               | Last Updated |
| ------------ | ------------- | -------------------------------------------------------------------- | ------------ |
| AWS          | c6i           | https://aws.amazon.com/ec2/pricing/on-demand/                        | Apr 2025     |
| GCP          | c2/n2         | https://cloud.google.com/compute/vm-instance-pricing                 | Apr 2025     |
| Azure        | Fsv2          | https://azure.microsoft.com/pricing/details/virtual-machines/series/ | Apr 2025     |
| DigitalOcean | CPU-Optimized | https://www.digitalocean.com/pricing/compute                         | Apr 2025     |
| Linode       | Dedicated CPU | https://www.linode.com/pricing/                                      | Apr 2025     |
| Hetzner      | CPX11         | https://www.hetzner.com/cloud/pricing                                | Apr 2026     |
