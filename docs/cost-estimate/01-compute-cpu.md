# Compute (CPU) cost estimation per node

> [!Note]
> This analysis assumes fully utilized block space for a conservative upper bound
> on costs. CPU timing values use **mainnet-average demand** (including organic
> Plutus usage) as measured by `db-analyser` on Cardano mainnet and fitted via
> OLS regression; see `docs/technical-report-2.md`. All timing values are also
> available in the CIP simulation configuration
> (`analysis/sims/cip/experiments/config.yaml`).

## Ouroboros Praos

We start with Ouroboros Praos to establish a baseline. In Praos, CPU utilization
comes from block header validation and transaction Apply, using the same
mainnet-average Apply cost as Leios for consistency.

| Component               | Validation Time | Source                                              |
| ----------------------- | --------------- | --------------------------------------------------- |
| Block header validation | 0.4438 ms       | `rb-head-validation-cpu-time-ms`; `db-analyser`     |
| Transaction Apply       | 0.6201 ms/tx    | `tx-validation-cpu-time-ms`; OLS on mainnet `Apply` |

### Block Rate Calculation

| Parameter               | Value    | Formula            |
| ----------------------- | -------- | ------------------ |
| Slot length             | 1 second | Protocol parameter |
| Active slot coefficient | 0.05     | Protocol parameter |
| **Blocks per second**   | **0.05** | $$1 \times 0.05$$  |

### Praos CPU Calculation (0.05 blocks/s)

A full 90 KB block contains $\lfloor 90{,}112 / 1{,}500 \rfloor \approx 60.07$ transactions.

$$C_{\text{praos}} = 0.05 \times \left(0.4438 + \frac{90{,}112}{1{,}500} \times 0.6201\right)$$

$$C_{\text{praos}} = 0.05 \times (0.4438 + 37.24) \approx 1.884\text{ ms/s}$$

Thus, Praos at 0.05 blocks/s consumes approximately 1.884 ms/s — about
**0.19% of a single CPU core** at mainnet-average demand.

> [!Note]
> The `Apply` cost of 0.6201 ms/tx comes from the OLS model fitted on actual
> mainnet blocks *without* explicitly separating the Plutus term, so it already
> embeds real organic Plutus demand. The `Reapply` path (0.137 ms/s, skipping
> Plutus re-execution) is used for archival chain replay and is not modeled
> here.

## Ouroboros Leios

In Linear Leios (CIP-164), CPU utilization comes from five components:
full transaction validation (`Apply`), ledger re-application (`Reapply`),
EB header validation, vote validation, and certificate validation.

### Apply vs. Reapply

Transactions in Leios are gossiped via the mempool and referenced by hash in
EBs. CPU is consumed in two distinct ways:

- **Apply (full validation)**: Performed when a transaction first arrives at a
  node (mempool ingestion). Includes signature verification and Plutus script
  evaluation. Cost: **0.6201 ms/tx** — the empirical mean Apply CPU time per
  transaction on Cardano mainnet since Epoch 350 (intercept-only OLS on
  `db-analyser` data; see `docs/technical-report-2.md`). Because it is a
  mean of observed blocks it already embeds real organic Plutus demand. To
  model explicit Plutus budgets, add 0.9487 ms/Gstep × exec\_Gstep on top.

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
| Transaction Apply (full)     | 0.6201 ms/tx              | `tx-validation-cpu-time-ms`; OLS on mainnet `Apply` (embeds avg Plutus) |
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

### CPU Usage Formulas

1. **Transaction Apply CPU** (scales with confirmed throughput):

   $$C_{\text{apply}} = \frac{\text{TxkB/s} \times 1{,}000}{S_{\text{tx}}} \times t_{\text{apply}}$$

   where $S_{\text{tx}} = 1{,}500$ bytes and $t_{\text{apply}} = 0.6201$ ms/tx.

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

1. **Tx Apply**: $\frac{4{,}500}{1{,}500} \times 0.6201 = 3 \times 0.6201 = 1.860\text{ ms/s}$

2. **Tx Reapply**: $0.0177 + 0.02151 \times 4.5 = 0.11\text{ ms/s}$

3. **EB Header**: $0.022\text{ ms/s}$

4. **Vote Validation**: $87.0\text{ ms/s}$

5. **Certificate Validation**: $7.86\text{ ms/s}$

6. **Total**:
   $$C_{\text{total}} = 1.860 + 0.11 + 0.022 + 87.0 + 7.86 = 96.85\text{ ms/s} \approx 9.7\%\text{ of one core}$$

At Praos-equivalent throughput, vote validation dominates (89.8% of CPU) due
to the fixed cost of validating 600 votes per EB regardless of transaction volume.

### CPU Utilization at Different Confirmed Throughputs

| TxkB/s | Tx/s | Tx Apply | Tx Reapply | EB Hdr | Vote   | Cert   | Total ms/s | % of One Core | Rec. Cores |
| ------ | ---- | -------- | ---------- | ------ | ------ | ------ | ---------- | ------------- | ---------- |
| 4.5    | 3    | 1.86ms   | 0.11ms     | 0.02ms | 87.0ms | 7.86ms | 96.85ms    | 9.7%          | 2          |
| 50     | 33   | 20.67ms  | 1.09ms     | 0.02ms | 87.0ms | 7.86ms | 116.6ms    | 11.7%         | 2          |
| 100    | 67   | 41.34ms  | 2.17ms     | 0.02ms | 87.0ms | 7.86ms | 138.4ms    | 13.8%         | 2          |
| 150    | 100  | 62.01ms  | 3.24ms     | 0.02ms | 87.0ms | 7.86ms | 160.1ms    | 16.0%         | 2          |
| 200    | 133  | 82.68ms  | 4.32ms     | 0.02ms | 87.0ms | 7.86ms | 181.9ms    | 18.2%         | 2          |
| 250    | 167  | 103.35ms | 5.39ms     | 0.02ms | 87.0ms | 7.86ms | 203.6ms    | 20.4%         | 2          |
| 300    | 200  | 124.02ms | 6.47ms     | 0.02ms | 87.0ms | 7.86ms | 225.4ms    | 22.5%         | 2          |

> [!Note]
>
> - Tx/s assumes average transaction size of 1,500 bytes
> - "% of One Core" = Total ms/s ÷ 1,000ms
> - Rec. Cores is 2 for all levels; 4 cores recommended for production to cover
>   GHC GC pressure, OS/network overhead, and burst load
> - Tx Apply uses the mainnet-average cost (embeds organic Plutus demand);
>   relays receiving EBs before individual txs only pay the cheaper Reapply cost

### CPU Component Analysis (at 200 TxkB/s)

| Component              | CPU Time | % of Total |
| ---------------------- | -------- | ---------- |
| Vote Validation        | 87.0ms   | 47.8%      |
| Tx Apply (full)        | 82.68ms  | 45.5%      |
| Certificate Validation | 7.86ms   | 4.3%       |
| Tx Reapply (ledger)    | 4.32ms   | 2.4%       |
| EB Header Validation   | 0.022ms  | < 0.1%     |

At 200 TxkB/s, vote validation (47.8%) and transaction Apply (45.5%) are
the two dominant components, with certificate validation now a visible
third (4.3%) after the P(cert) fix.

### Comparative Efficiency (Leios vs. Praos)

| TxkB/s | Leios CPU (ms/s) | CPU per TxkB/s (ms) | Praos CPU per TxkB/s (ms) | Leios:Praos ratio |
| ------ | ---------------- | ------------------- | ------------------------- | ----------------- |
| 4.5    | 96.85ms          | 21.5                | 0.419                     | 51:1              |
| 50     | 116.6ms          | 2.33                | 0.419 (does not scale)    | 5.6:1             |
| 100    | 138.4ms          | 1.38                | —                         | 3.3:1             |
| 200    | 181.9ms          | 0.91                | —                         | 2.2:1             |
| 300    | 225.4ms          | 0.75                | —                         | 1.8:1             |

The high Leios:Praos ratio at low throughput is dominated by the fixed vote
overhead (87 ms/s). As confirmed throughput grows, the ratio drops toward
~1.8:1 at 300 TxkB/s, where Leios delivers 67× more confirmed throughput
while using only ~14× more absolute CPU.

## Monthly Cost by Cloud Provider ($)

Using standard compute-optimized instances. 2 cores satisfies the CPU
requirement at all modeled throughput levels; 4 cores recommended for
production deployments.

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

1. **CPU floor**: 2 cores covers all throughput levels up to 300 TxkB/s
   (peak 22.5% of one core at mainnet-average demand)
2. **Production**: 4 cores recommended to handle GHC GC, UTxO-HD I/O waits,
   and burst conditions — consistent with the CIP-164 hardware recommendation
3. **Above 300 TxkB/s**: Additional cores needed for transaction Apply
   parallelism
4. **Plutus-heavy workloads**: Workloads with higher-than-average Plutus usage
   will require proportionally more CPU; add 0.9487 ms/Gstep × exec\_budget
   per transaction on top of the base 0.6201 ms/tx

> [!Important]
>
> Real-world performance may require more cores due to:
>
> - GHC garbage collector pressure (especially during protocol burst attacks)
> - Disk I/O wait for UTxO-HD ledger state access
> - Uneven workload distribution across stages
> - Plutus-heavy workloads exceeding mainnet-average execution budget
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
