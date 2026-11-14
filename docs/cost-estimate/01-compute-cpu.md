# Compute (CPU) cost estimation per node

> [!Note]
> This analysis assumes fully utilized block space at each throughput. Tx apply uses **mainnet-average demand** (including organic Plutus
> usage) as measured by `db-analyser` on Cardano mainnet and fitted via OLS
> regression; see `docs/technical-report-2.md`. Header validation is a
> `db-analyser` measurement. Both are also in the CIP simulation configuration
> (`analysis/sims/cip/experiments/config.yaml`). Tx reapply and EB closure
> validation come from the
> [feasibility report](https://github.com/input-output-hk/ouroboros-leios/pull/1156):
> reapply as measured in its voting loop on c5d hosts, and the fixed 20 ms per EB
> it uses to rebuild validation times.

## Ouroboros Praos

We start with Ouroboros Praos to establish a baseline. In Praos, CPU utilization
comes from block header validation and transaction Apply, which a node runs
twice per transaction: when the transaction enters its mempool, and again when
the block that carries it is adopted, because chain selection validates in full
every block the node has not validated before (`ApplyVal` in
ouroboros-consensus). Praos uses the same mainnet-average Apply cost as Leios.

| Component               | Validation Time | Source                                              |
| ----------------------- | --------------- | --------------------------------------------------- |
| Block header validation | 0.4438 ms       | `rb-head-validation-cpu-time-ms`; `db-analyser`     |
| Transaction Apply       | 0.6201 ms/tx    | `tx-validation-cpu-time-ms`; OLS on mainnet `Apply` |
| Block adoption          | 0.6201 ms/tx    | The same full validation, run again on adoption     |

### Block Rate Calculation

| Parameter               | Value    | Formula            |
| ----------------------- | -------- | ------------------ |
| Slot length             | 1 second | Protocol parameter |
| Active slot coefficient | 0.05     | Protocol parameter |
| **Blocks per second**   | **0.05** | $$1 \times 0.05$$  |

### Praos CPU Calculation (0.05 blocks/s)

A full 90 KB block contains $90{,}112 / 1{,}132 \approx 79.60$ transactions.

$$C_{\text{praos}} = 0.05 \times \left(0.4438 + 2 \times \frac{90{,}112}{1{,}132} \times 0.6201\right)$$

$$C_{\text{praos}} = 0.05 \times (0.4438 + 98.72) \approx 4.958\text{ ms/s}$$

Thus, Praos at 0.05 blocks/s consumes approximately 4.958 ms/s, about
**0.50% of a single CPU core** at mainnet-average demand.

> [!Note]
> The `Apply` cost of 0.6201 ms/tx comes from the OLS model fitted on actual
> mainnet blocks *without* explicitly separating the Plutus term, so it already
> embeds real organic Plutus demand.

## Ouroboros Leios

In Linear Leios (CIP-164), CPU utilization comes from six components:
full transaction validation (`Apply`), block adoption, EB closure validation,
EB header validation, vote validation, and certificate validation.

### Apply vs. Reapply

Transactions in Leios are gossiped via the mempool and referenced by hash in
EBs. CPU is consumed in three ways:

- **Apply (full validation)**: Performed when a transaction first arrives at a
  node (mempool ingestion). Includes signature verification and Plutus script
  evaluation. Cost: **0.6201 ms/tx** — the empirical mean Apply CPU time per
  transaction on Cardano mainnet since Epoch 350 (intercept-only OLS on
  `db-analyser` data; see `docs/technical-report-2.md`). Because it is a
  mean of observed blocks it already embeds real organic Plutus demand. To
  model explicit Plutus budgets, use the same report's fit with a Plutus term
  in its place: 0.2624 ms/tx + 0.9487 ms/Gstep × exec\_Gstep.

- **Block adoption**: Performed when the block that carries a transaction is
  adopted. A transaction in an RB body is validated in full again, as in Praos
  (consensus `ApplyVal`), at the `Apply` cost. A transaction in a certified EB's
  closure is reapplied (`ValidateNone`): the ledger is updated with the
  signature and Plutus checks skipped. Reapply cost: **0.147 ms/tx**, the lowest
  reapply cost the
  [feasibility report](https://github.com/input-output-hk/ouroboros-leios/pull/1156)
  measured in its voting loop, on c5d hosts; its regressions give 0.19 to
  0.21 ms/tx. The report times the closure's adoption itself at 0.04 to
  0.11 ms/tx, so for adoption 0.147 ms is a conservative bound.

- **EB closure validation**: Validating an announced EB's closure before voting.
  It reapplies the EB's transactions from the mempool. Cost: **20 ms per EB +
  0.147 ms/tx**: the fixed per-EB part the feasibility report uses to rebuild
  validation times, plus its measured reapply cost. This estimate charges it to
  every block producer for every announced EB, certified or not; relays don't
  vote, so they skip it.

For this cost estimate every node pays the `Apply` cost once for every
confirmed transaction, at mempool ingestion, and a block producer also pays the
`Reapply` cost in the closure of every announced EB that carries it, about
$1/P_{\text{cert}} \approx 2$ times. On adoption it pays the `Apply` cost again
for a transaction in an RB body, as Praos does for every transaction, and the
`Reapply` cost for one in a certified closure. A transaction that reaches a
node only inside an EB is applied during closure validation instead, at the
`Apply` cost.

### Component Processing Times

| Component                    | Cost                        | Config Reference                                                        |
|------------------------------|-----------------------------|-------------------------------------------------------------------------|
| Transaction Apply (full)     | 0.6201 ms/tx                | `tx-validation-cpu-time-ms`; OLS on mainnet `Apply` (embeds avg Plutus) |
| Transaction Reapply (ledger) | 0.147 ms/tx                 | Feasibility report (PR #1156): voting loop, c5d hosts                   |
| EB closure validation        | 20 ms/EB + 0.147 ms/tx      | Feasibility report (PR #1156): per-EB rebuild constant + reapply        |
| EB header validation         | 0.4438 ms/EB                | `eb-header-validation-cpu-time-ms`                                      |
| Vote validation              | 0.67 ms/vote                | One BLS signature check, stake-based committee (Rust benchmark, 2025)   |
| Certificate validation       | 0.9 ms + 1.9 µs × seats     | Haskell `verifyLeiosCert` (2026-10): 2.04 ms at 600 seats               |

### Base Parameters

| Parameter       | Value       | Source                                                                          |
|-----------------|-------------|---------------------------------------------------------------------------------|
| EB rate         | 0.05 EB/s   | Active slot coefficient                                                         |
| Votes per EB    | 600         | Committee seats: one vote per seat per EB; 600 for launch, below CIP-164's 900, to limit vote traffic (about 95% of active stake) |
| P(EB certified) | 0.513       | $(1 - 0.05)^{13}$: the next RB comes 14 or more slots later ($3L_{\text{hdr}} + L_{\text{vote}} + L_{\text{diff}}$ = 3 + 4 + 7), so none in the 13 between |
| Average tx size | 1,132 bytes | Mainnet mean, epochs 589–661 (db-sync)                                          |

### CPU Usage Formulas

1. **Transaction Apply CPU** (scales with confirmed throughput):

   $$C_{\text{apply}} = \frac{\text{TxkB/s} \times 1{,}000}{S_{\text{tx}}} \times t_{\text{apply}}$$

   where $S_{\text{tx}} = 1{,}132$ bytes and $t_{\text{apply}} = 0.6201$ ms/tx.

2. **Block Adoption CPU** (scales with throughput): RBs without a certificate
   carry a full body, $0.05 \times (1 - P_{\text{cert}}) \times 90{,}112 \approx 2{,}193$ B/s,
   whose transactions are applied again; the rest arrive in certified closures
   and are reapplied:

   $$C_{\text{adopt}} = \frac{2{,}193 \times 0.6201 + (\text{TxkB/s} \times 1{,}000 - 2{,}193) \times 0.147}{S_{\text{tx}}}$$

3. **EB Closure Validation CPU** (every announced EB, scales with throughput):

   $$C_{\text{closure}} = R_{\text{eb}} \times \left(20 + N_{\text{eb}} \times 0.147\right)$$

   where $R_{\text{eb}} = 0.05$ EB/s and $N_{\text{eb}}$ is the number of
   transactions in each announced EB. Only certified EBs reach the ledger, and an
   RB without a certificate carries a full 90,112 B body, so each announced EB
   carries

   $$N_{\text{eb}} = \frac{\text{TxkB/s} \times 1{,}000 / R_{\text{eb}} - (1 - P_{\text{cert}}) \times 90{,}112}{P_{\text{cert}} \times S_{\text{tx}}}$$

   about $1/P_{\text{cert}} \approx 2$ times what certified EBs alone would need.

4. **EB Header Validation CPU** (fixed):

   $$C_{\text{eb}} = 0.05 \times 0.4438 = 0.022\text{ ms/s}$$

5. **Vote Validation CPU** (fixed):

   $$C_{\text{vote}} = 600 \times 0.05 \times 0.67 = 20.1\text{ ms/s}$$

6. **Certificate Validation CPU** (fixed, certified EBs only):

   $$C_{\text{cert}} = 0.05 \times 0.513 \times (0.9 + 0.0019 \times 600) = 0.05\text{ ms/s}$$

7. **Total CPU**:

   $$C_{\text{total}} = C_{\text{apply}} + C_{\text{adopt}} + C_{\text{closure}} + C_{\text{eb}} + C_{\text{vote}} + C_{\text{cert}}$$

### CPU Calculation at 5 TxkB/s (Leios Baseline)

The lowest meaningful Leios operating point: just above the Praos capacity
ceiling (4.5 TxkB/s). For comparison, Praos at 4.5 TxkB/s requires only
4.958 ms/s (0.50% of one core; see [Praos section](#ouroboros-praos)).

1. **Tx Apply**: $\frac{5{,}000}{1{,}132} \times 0.6201 = 4.42 \times 0.6201 = 2.74\text{ ms/s}$

2. **Block Adoption**: $\frac{2{,}193 \times 0.6201 + 2{,}807 \times 0.147}{1{,}132} = 1.57\text{ ms/s}$

3. **EB Closure Validation**: $N_{\text{eb}} = \frac{100{,}000 - 43{,}857}{0.5133 \times 1{,}132} \approx 96.6$, so $0.05 \times (20 + 96.6 \times 0.147) = 1.71\text{ ms/s}$

4. **EB Header**: $0.022\text{ ms/s}$

5. **Vote Validation**: $20.1\text{ ms/s}$

6. **Certificate Validation**: $0.05\text{ ms/s}$

7. **Total**:
   $$C_{\text{total}} = 2.74 + 1.57 + 1.71 + 0.022 + 20.1 + 0.05 = 26.2\text{ ms/s} \approx 2.6\%\text{ of one core}$$

At this baseline, a Leios block producer requires ~5× more CPU than Praos at
4.5 TxkB/s (26.2 ms/s vs 4.958 ms/s), with the fixed vote validation overhead
(20.1 ms/s) accounting for most of the difference. A relay skips the closure
validation.

### CPU Utilization at Different Confirmed Throughputs

| TxkB/s        | Tx/s | Tx Apply  | Adoption   | Closure | EB Hdr | Vote   | Cert   | Total ms/s | % of One Core | Rec. Cores |
| ------------- | ---- | --------- | ---------- | ------- | ------ | ------ | ------ | ---------- | ------------- | ---------- |
| 4.5 (Praos)   | 4    | 2.47ms    | 2.47ms     | —       | —      | —      | —      | **4.96ms** | **0.50%**     | 2          |
| 5             | 4    | 2.74ms    | 1.57ms     | 1.71ms  | 0.02ms | 20.1ms | 0.05ms | 26.2ms     | 2.6%          | 2          |
| 50            | 44   | 27.39ms   | 7.41ms     | 13.09ms | 0.02ms | 20.1ms | 0.05ms | 68.1ms     | 6.8%          | 2          |
| 100           | 88   | 54.78ms   | 13.90ms    | 25.74ms | 0.02ms | 20.1ms | 0.05ms | 114.6ms    | 11.5%         | 2          |
| 200           | 177  | 109.56ms  | 26.89ms    | 51.04ms | 0.02ms | 20.1ms | 0.05ms | 207.7ms    | 20.8%         | 2          |
| 300           | 265  | 164.34ms  | 39.87ms    | 76.34ms | 0.02ms | 20.1ms | 0.05ms | 300.7ms    | 30.1%         | 2          |

> [!Note]
>
> - Leios rows are a block producer's; a relay's total is the same without the
>   Closure column
> - The 4.5 (Praos) row shows the Praos protocol at its normal operating point.
>   Leios announces no EBs at or below Praos capacity, so at this load it costs
>   the same as Praos
> - Tx/s assumes average transaction size of 1,132 bytes
> - "% of One Core" = Total ms/s ÷ 1,000ms
> - All rows: 2 cores minimum, cardano-node's minimum system requirement; 4 cores
>   recommended for production to cover GHC GC pressure, OS/network overhead, and
>   burst load
> - Tx Apply, and the adoption of RB-body transactions, use the mainnet-average
>   cost (embeds organic Plutus demand); the adoption of certified closures and
>   Closure use the feasibility report's figures

### Comparative Efficiency (Leios vs. Praos)

| TxkB/s      | CPU (ms/s)      | CPU per TxkB/s (ms) | Praos CPU per TxkB/s (ms) | Ratio |
| ----------- | --------------- | ------------------- | ------------------------- | ----- |
| 4.5 (Praos) | 4.958ms (Praos) | 1.10                | 1.10                      | 1:1    |
| 5           | 26.2ms          | 5.24                | 1.10                      | 4.75:1 |
| 50          | 68.1ms          | 1.36                | 1.10 (does not scale)     | 1.24:1 |
| 100         | 114.6ms         | 1.15                | —                         | 1.04:1 |
| 200         | 207.7ms         | 1.04                | —                         | 0.94:1 |
| 300         | 300.7ms         | 1.00                | —                         | 0.91:1 |

The Praos row shows 1:1 because at 4.5 TxkB/s Praos IS the baseline. Moving
to Leios at 5 TxkB/s jumps to 4.75:1: the fixed vote overhead (20.1 ms/s)
dominates at near-Praos loads. As confirmed throughput grows, the ratio falls
below 1:1 from about 126 TxkB/s, reaching 0.91:1 at 300 TxkB/s: 67× the
confirmed throughput of Praos for 61× its CPU. Praos validates every
transaction in full twice, in the mempool and in the block; Leios validates it
in full once and reapplies it after.

## Monthly Cost by Cloud Provider ($)

Using the 2 vCPU shapes behind the cost estimator's price presets and their
4 vCPU counterparts, at on-demand list prices checked on 2026-11-10 (Akamai's
preset uses its Dedicated G7 4 vCPU / 8 GB plan; its G6 Dedicated 8 GB costs $72 for
the same shape, and a 2 vCPU G8 Dedicated 8 GB plan exists). 2 cores
satisfies the CPU requirement at all modeled throughput levels; 4 cores
recommended for production deployments.

| Provider                     | 2 Core  | 4 Core  | Notes                                                  |
| ---------------------------- | ------- | ------- | ------------------------------------------------------ |
| AWS m7i                      | $73.58  | $147.17 | m7i.large / m7i.xlarge, 8 / 16 GiB, on-demand          |
| GCP e2-standard              | $48.92  | $97.84  | e2-standard-2 / e2-standard-4, 8 / 16 GB, on-demand    |
| Azure Dasv6                  | $66.28  | $132.86 | D2as v6 / D4as v6, 8 / 16 GiB, on-demand               |
| DigitalOcean General Purpose | $63.00  | $126.00 | g-2vcpu-8gb / g-4vcpu-16gb                             |
| Akamai (Linode) Dedicated G7 | $43.00  | $86.00  | 2 vCPU / 4 GB and 4 vCPU / 8 GB plans                  |
| Hetzner CCX                  | $48.77  | $96.99  | CCX13 / CCX23, 8 / 16 GB; EUR at 1 EUR = 1.1214 USD    |

> [!Note]
>
> - Prices are for US regions (Hetzner: Germany) and may vary by location
> - Assumes on-demand general-purpose instances, or the dedicated-CPU plans of
>   Akamai and Hetzner
> - Does not include potential savings from reserved instances or spot pricing

## Recommendations

1. **CPU floor**: 2 cores covers all throughput levels up to 300 TxkB/s
   (peak 30.1% of one core at mainnet-average demand)
2. **Production**: 4 cores recommended to handle GHC GC, disk I/O waits
   (UTxO-HD), and burst conditions — consistent with the CIP-164 hardware
   recommendation
3. **Above about 190 TxkB/s**: Faster cores would be needed
4. **Plutus-heavy workloads**: Workloads with higher-than-average Plutus usage
   will require proportionally more CPU; price them at 0.2624 ms/tx +
   0.9487 ms/Gstep × exec\_budget per transaction, in place of 0.6201 ms/tx

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
| AWS          | m7i             | https://aws.amazon.com/ec2/pricing/on-demand/                        | Nov 2026     |
| GCP          | e2-standard     | https://cloud.google.com/compute/vm-instance-pricing                 | Nov 2026     |
| Azure        | Dasv6           | https://azure.microsoft.com/pricing/details/virtual-machines/series/ | Nov 2026     |
| DigitalOcean | General Purpose | https://www.digitalocean.com/pricing/compute                         | Nov 2026     |
| Akamai (Linode) | Dedicated G7 | https://www.linode.com/pricing/                                      | Nov 2026     |
| Hetzner      | CCX13 / CCX23   | https://www.hetzner.com/cloud/pricing                                | Nov 2026     |
