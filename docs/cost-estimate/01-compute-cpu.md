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

| Component                    | Cost                        | Config Reference                                                        |
|------------------------------|-----------------------------|-------------------------------------------------------------------------|
| Transaction Apply (full)     | 0.6201 ms/tx                | `tx-validation-cpu-time-ms`; OLS on mainnet `Apply` (embeds avg Plutus) |
| Transaction Reapply (ledger) | 0.3539 ms + 0.00002151 ms/B | `eb-body-validation-cpu-time-ms-*`                                      |
| EB header validation         | 0.4438 ms/EB                | `eb-header-validation-cpu-time-ms`                                      |
| Vote validation              | 2.9 ms/vote                 | `vote-validation-cpu-time-ms`; non-persistent worst case                |
| Certificate validation       | 157.2 ms/cert               | `cert-validation-cpu-time-ms-constant`                                  |

### Base Parameters

| Parameter       | Value       | Source                                                                          |
|-----------------|-------------|---------------------------------------------------------------------------------|
| EB rate         | 0.05 EB/s   | Active slot coefficient                                                         |
| Votes per EB    | 600         | `vote-generation-probability`; wFA+LS committee                                 |
| Average tx size | 1,500 bytes | Conservative estimate                                                           |

### CPU Usage Formulas

1. **Transaction Apply CPU** (scales with confirmed throughput):

   $$C_{\text{apply}} = \frac{\text{TxkB/s} \times 1{,}000}{S_{\text{tx}}} \times t_{\text{apply}}$$

   where $S_{\text{tx}} = 1{,}500$ bytes and $t_{\text{apply}} = 0.6201$ ms/tx.

2. **Transaction Reapply CPU** (per EB, scales with throughput):

   $$C_{\text{reapply}} = R_{\text{eb}} \times \left(0.3539 + 0.00002151 \times \frac{\text{TxkB/s} \times 1{,}000}{R_{\text{eb}}}\right)$$

   Simplifying (where $R_{\text{eb}} = 0.05$ EB/s):

   $$C_{\text{reapply}} = 0.0177 + 0.02151 \times \text{TxkB/s} \text{ ms/s}$$

3. **EB Header Validation CPU** (fixed):

   $$C_{\text{eb}} = 0.05 \times 0.4438 = 0.022\text{ ms/s}$$

4. **Vote Validation CPU** (fixed):

   $$C_{\text{vote}} = 600 \times 0.05 \times 2.9 = 87.0\text{ ms/s}$$

5. **Certificate Validation CPU** (fixed):

   $$C_{\text{cert}} = 0.05 \times 157.2 = 7.86\text{ ms/s}$$

6. **Total CPU**:

   $$C_{\text{total}} = C_{\text{apply}} + C_{\text{reapply}} + C_{\text{eb}} + C_{\text{vote}} + C_{\text{cert}}$$

### CPU Calculation at 5 TxkB/s (Leios Baseline)

The lowest meaningful Leios operating point: just above the Praos capacity
ceiling (4.5 TxkB/s). For comparison, Praos at 4.5 TxkB/s requires only
1.884 ms/s (0.19% of one core; see [Praos section](#ouroboros-praos)).

1. **Tx Apply**: $\frac{5{,}000}{1{,}500} \times 0.6201 = 3.33 \times 0.6201 = 2.07\text{ ms/s}$

2. **Tx Reapply**: $0.0177 + 0.02151 \times 5 = 0.13\text{ ms/s}$

3. **EB Header**: $0.022\text{ ms/s}$

4. **Vote Validation**: $87.0\text{ ms/s}$

5. **Certificate Validation**: $7.86\text{ ms/s}$

6. **Total**:
   $$C_{\text{total}} = 2.07 + 0.13 + 0.022 + 87.0 + 7.86 = 97.1\text{ ms/s} \approx 9.7\%\text{ of one core}$$

At this baseline, Leios requires ~52× more CPU than Praos at 4.5 TxkB/s
(97.1 ms/s vs 1.884 ms/s), with the fixed vote validation overhead (87.0 ms/s)
accounting for almost the entire difference.

### CPU Utilization at Different Confirmed Throughputs

| TxkB/s        | Tx/s | Tx Apply  | Tx Reapply | EB Hdr | Vote   | Cert   | Total ms/s | % of One Core | Rec. Cores |
| ------------- | ---- | --------- | ---------- | ------ | ------ | ------ | ---------- | ------------- | ---------- |
| 4.5 (Praos)   | 3    | 1.86ms    | —          | —      | —      | —      | **1.88ms** | **0.19%**     | 1          |
| 5             | 3    | 2.07ms    | 0.13ms     | 0.02ms | 87.0ms | 7.86ms | 97.1ms     | 9.7%          | 2          |
| 50            | 33   | 20.67ms   | 1.09ms     | 0.02ms | 87.0ms | 7.86ms | 116.6ms    | 11.7%         | 2          |
| 100           | 67   | 41.34ms   | 2.17ms     | 0.02ms | 87.0ms | 7.86ms | 138.4ms    | 13.8%         | 2          |
| 200           | 133  | 82.68ms   | 4.32ms     | 0.02ms | 87.0ms | 7.86ms | 181.9ms    | 18.2%         | 2          |
| 300           | 200  | 124.02ms  | 6.47ms     | 0.02ms | 87.0ms | 7.86ms | 225.4ms    | 22.5%         | 2          |

> [!Note]
>
> - The 4.5 (Praos) row shows the Praos protocol at its normal operating point;
>   Leios Tx Apply at the same load would be identical, but fixed vote and
>   certificate overhead add ~95 ms/s on top
> - Tx/s assumes average transaction size of 1,500 bytes
> - "% of One Core" = Total ms/s ÷ 1,000ms
> - Leios rows: 2 cores minimum; 4 cores recommended for production to cover
>   GHC GC pressure, OS/network overhead, and burst load
> - Tx Apply uses the mainnet-average cost (embeds organic Plutus demand);
>   relays receiving EBs before individual txs only pay the cheaper Reapply cost

### Comparative Efficiency (Leios vs. Praos)

| TxkB/s      | CPU (ms/s)      | CPU per TxkB/s (ms) | Praos CPU per TxkB/s (ms) | Ratio |
| ----------- | --------------- | ------------------- | ------------------------- | ----- |
| 4.5 (Praos) | 1.884ms (Praos) | 0.419               | 0.419                     | 1:1   |
| 5           | 97.1ms          | 19.4                | 0.419                     | 46:1  |
| 50          | 116.6ms         | 2.33                | 0.419 (does not scale)    | 5.6:1 |
| 100         | 138.4ms         | 1.38                | —                         | 3.3:1 |
| 200         | 181.9ms         | 0.91                | —                         | 2.2:1 |
| 300         | 225.4ms         | 0.75                | —                         | 1.8:1 |

The Praos row shows 1:1 because at 4.5 TxkB/s Praos IS the baseline. Moving
to Leios at 5 TxkB/s jumps to 46:1 — the fixed vote overhead (87 ms/s)
dominates at near-Praos loads. As confirmed throughput grows, the ratio drops
toward ~1.8:1 at 300 TxkB/s, where Leios delivers 67× more confirmed
throughput while using only ~14× more absolute CPU.

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
2. **Production**: 4 cores recommended to handle GHC GC, disk I/O waits
   (UTxO-HD), and burst conditions — consistent with the CIP-164 hardware
   recommendation
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
