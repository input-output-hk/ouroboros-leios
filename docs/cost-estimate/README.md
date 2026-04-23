# Leios Node Operating Costs Analysis

## Overview

This document provides a list of cost items used for our analysis of the
operational costs associated with running a Leios node. As a baseline we use
Ouroboros Praos for comparisons. All cost estimates are for **Linear Leios
(CIP-164)** and assume fully confirmed transaction throughput (TxkB/s —
transaction kilobytes per second reaching the ledger). Costs represent
conservative upper bounds: 3,000 votes per EB (all active pools), individual
BLS vote verification, 100% confirmed block utilization, and **full Plutus
execution unit utilization per transaction** (20 Gstep/tx — the per-tx
maximum; real-world CPU costs will be lower).

The primary throughput metric is **confirmed TxkB/s**, derived from the
CIP-164 design where:
- EBs reference transactions by 32-byte hash at 0.05 EB/s
- Transactions are gossiped via the mempool (not bundled in IBs)
- $P(\text{EB certified}) \approx 0.48$ sets the capacity ceiling at ~288 TxkB/s

## Cost Items

| Cost Item                             | Unit      | Description                                |
| ------------------------------------- | --------- | ------------------------------------------ |
| [Compute (vCPU)](./01-compute-cpu.md) | $/vCPU/h  | Cost per virtual CPU per hour              |
| [Compute (RAM)](./02-compute-ram.md)  | $/GB/h    | Cost per gigabyte of RAM per hour          |
| [Storage (SSD)](./03-storage.md)      | $/GiB/mo  | Cost per gibibyte of SSD storage per month |
| [Egress](./04-egress.md)              | $/GiB     | Cost per gibibyte of data transferred out  |
| [IOPS](./05-iops.md)                  | $/IOPS/mo | Cost per IOPS per month                    |

Follow the links above to see detailed cost estimates per item.

## Aggregated Total Cost Table

The table below provides an aggregated summary of all cost categories across
different cloud providers based on confirmed throughput in TxkB/s.

| Provider         | Cost Item           | 4.5 TxkB/s | 50 TxkB/s  | 100 TxkB/s  | 150 TxkB/s  | 200 TxkB/s  | 250 TxkB/s  | 300 TxkB/s  |
| ---------------- | ------------------- | ---------- | ---------- | ----------- | ----------- | ----------- | ----------- | ----------- |
| **AWS**          | Compute (vCPU)      | $62.05     | $62.05     | $62.05      | $124.10     | $124.10     | $124.10     | $124.10     |
|                  | Compute (RAM)       | $20.79     | $20.79     | $20.79      | $20.79      | $20.79      | $20.79      | $20.79      |
|                  | Storage             | $0.00      | $2.71      | $13.34      | $23.96      | $34.58      | $45.20      | $55.83      |
|                  | Egress              | $0.00      | $52.36     | $112.03     | $171.68     | $231.35     | $291.02     | $350.68     |
|                  | IOPS                | $10.00     | $10.00     | $10.00      | $10.00      | $10.00      | $10.00      | $10.00      |
|                  | **Total (AWS)**     | **$92.84** | **$147.91**| **$218.21** | **$350.53** | **$420.82** | **$491.11** | **$561.40** |
| **GCP**          | Compute (vCPU)      | $52.34     | $52.34     | $52.34      | $152.35     | $152.35     | $152.35     | $152.35     |
|                  | Compute (RAM)       | $35.95     | $35.95     | $35.95      | $35.95      | $35.95      | $35.95      | $35.95      |
|                  | Storage             | $0.52      | $5.36      | $10.67      | $15.98      | $21.29      | $26.60      | $31.92      |
|                  | Egress              | $9.42      | $81.82     | $161.37     | $240.91     | $320.47     | $400.02     | $479.57     |
|                  | IOPS                | $15.00     | $15.00     | $15.00      | $15.00      | $15.00      | $15.00      | $15.00      |
|                  | **Total (GCP)**     | **$113.23**| **$190.47**| **$275.33** | **$460.19** | **$545.06** | **$629.92** | **$714.79** |
| **Azure**        | Compute (vCPU)      | $61.76     | $61.76     | $61.76      | $123.37     | $123.37     | $123.37     | $123.37     |
|                  | Compute (RAM)       | $19.50     | $19.50     | $19.50      | $19.50      | $19.50      | $19.50      | $19.50      |
|                  | Storage             | $0.00      | $2.54      | $12.50      | $22.46      | $32.42      | $42.38      | $52.34      |
|                  | Egress              | $0.00      | $50.62     | $108.29     | $165.96     | $223.64     | $281.31     | $338.99     |
|                  | IOPS                | $12.00     | $12.00     | $12.00      | $12.00      | $12.00      | $12.00      | $12.00      |
|                  | **Total (Azure)**   | **$93.26** | **$146.42**| **$214.05** | **$343.29** | **$410.93** | **$478.56** | **$546.20** |
| **DigitalOcean** | Compute (vCPU)      | $42.00     | $42.00     | $42.00      | $84.00      | $84.00      | $84.00      | $84.00      |
|                  | Compute (RAM)       | $16.28     | $16.28     | $16.28      | $16.28      | $16.28      | $16.28      | $16.28      |
|                  | Storage             | $0.00      | $3.39      | $16.67      | $29.95      | $43.22      | $56.50      | $69.79      |
|                  | Egress              | $0.00      | $0.00      | $3.45       | $10.08      | $16.71      | $23.34      | $29.96      |
|                  | IOPS                | $8.00      | $8.00      | $8.00       | $8.00       | $8.00       | $8.00       | $8.00       |
|                  | **Total (DO)**      | **$66.28** | **$69.67** | **$86.40**  | **$148.31** | **$168.21** | **$188.12** | **$208.03** |
| **Linode**       | Compute (vCPU)      | $36.00     | $36.00     | $36.00      | $60.00      | $60.00      | $60.00      | $60.00      |
|                  | Compute (RAM)       | $21.75     | $21.75     | $21.75      | $21.75      | $21.75      | $21.75      | $21.75      |
|                  | Storage             | $0.00      | $0.00      | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       |
|                  | Egress              | $0.00      | $0.00      | $1.60       | $4.92       | $8.23       | $11.55      | $14.86      |
|                  | IOPS                | $7.00      | $7.00      | $7.00       | $7.00       | $7.00       | $7.00       | $7.00       |
|                  | **Total (Linode)**  | **$64.75** | **$64.75** | **$66.35**  | **$93.67**  | **$96.98**  | **$100.30** | **$103.61** |
| **Hetzner**      | Compute (vCPU)      | $6.59      | $6.59      | $6.59       | $17.80      | $17.80      | $17.80      | $17.80      |
|                  | Compute (RAM)       | $4.39      | $4.39      | $4.39       | $4.39       | $4.39       | $4.39       | $4.39       |
|                  | Storage             | $0.83      | $8.44      | $16.80      | $25.17      | $33.53      | $41.89      | $50.26      |
|                  | Egress              | $0.00      | $0.00      | $0.35       | $1.08       | $1.81       | $2.54       | $3.27       |
|                  | IOPS                | $5.00      | $5.00      | $5.00       | $5.00       | $5.00       | $5.00       | $5.00       |
|                  | **Total (Hetzner)** | **$16.81** | **$24.42** | **$33.13**  | **$53.44**  | **$62.53**  | **$71.62**  | **$80.72**  |

> [!Note]
> All costs are monthly estimates in USD ($) based on confirmed throughput in
> TxkB/s (transaction kilobytes per second reaching the ledger).
>
> - The 4.5 TxkB/s column corresponds to Praos-equivalent throughput
>   (0.05 blocks/s × 90 KiB = 4.5 TxkB/s)
> - Compute (vCPU) uses the 2-core tier for ≤100 TxkB/s and the 4-core tier
>   for 150+ TxkB/s; at 300 TxkB/s the 4-core tier is fully utilized (402% of
>   one core) — 6+ cores recommended for production headroom
>   (see [01-compute-cpu.md](./01-compute-cpu.md))
> - At higher throughput, egress dominates for premium cloud providers;
>   budget providers (Hetzner, Linode) remain affordable due to generous
>   included transfer
> - Fixed vote overhead (600 votes × 164 B × 0.05 EB/s) contributes ~12 GiB/month
>   in egress regardless of confirmed throughput; vote count is based on the
>   wFA+LS committee scheme from the CIP simulation config

> [!Important] 
> Storage costs shown above represent only one month of blockchain data. As
> blockchain history accumulates over time, storage requirements and associated
> costs will continuously increase.

> [!Note] 
> Storage and data transfer use binary prefixes (GiB = 2³⁰ bytes), while RAM
> uses decimal prefixes (GB = 10⁹ bytes), following industry standards for
> cloud computing.

## Cost/Revenue Analysis

This section analyzes potential revenue from transaction fees based on the
current Cardano mainnet fee calculation formula at different throughput levels.

### Fee Calculation Formula

Cardano calculates transaction fees using the formula:

$$\text{Fee} = a + (b \times \text{size})$$

Where:
- $a$ = 155,381 Lovelace (0.155381 ADA) — fixed minimum fee per transaction
- $b$ = 44.0576 Lovelace per byte (0.0000440576 ADA per byte) — fee per byte
- $\text{size}$ = transaction size in bytes

At the assumed average of 1,500 bytes:

$$\text{Fee} = 0.155381 + (0.0000440576 \times 1{,}500) = 0.221467 \text{ ADA/tx}$$

### Throughput and Revenue at Different Confirmed Rates

| TxkB/s | Tx/s (1,500 B avg) | Monthly Txs     | Fee/Tx (ADA) | Monthly Revenue (ADA) |
| ------ | ------------------ | --------------- | ------------ | --------------------- |
| 4.5    | 3                  | 7,884,000       | 0.221467     | 1,745,932             |
| 50     | 33                 | 86,724,000      | 0.221467     | 19,205,255            |
| 100    | 67                 | 176,076,000     | 0.221467     | 38,991,426            |
| 150    | 100                | 262,800,000     | 0.221467     | 58,201,412            |
| 200    | 133                | 349,524,000     | 0.221467     | 77,411,397            |
| 250    | 167                | 438,876,000     | 0.221467     | 97,197,568            |
| 300    | 200                | 525,600,000     | 0.221467     | 116,402,822           |

> [!Important]
> The revenue figures above represent **total network revenue**, while cost
> figures in the [Aggregated Total Cost Table](#aggregated-total-cost-table)
> represent costs for **individual nodes**. In a decentralized network with
> approximately 3,000 stake pool operators (SPOs), each typically running
> multiple nodes, the total network infrastructure cost would be significantly
> higher. A proper economic analysis must consider that:
>
> 1. Each SPO only receives a portion of the total fees, proportional to their
>    stake in the network
> 2. The total network infrastructure cost would be ~9,000+ nodes (3,000 SPOs ×
>    3 nodes each, plus additional relay infrastructure)
> 3. Revenue distribution mechanisms and network parameters ultimately determine
>    individual operator profitability

### TPS Breakeven Analysis for Network Infrastructure

To maintain the current network reward structure as the Reserve depletes, we
can calculate the required confirmed throughput to cover the operational costs
of all network participants.

Assumptions:
- Approximately 3,000 stake pool operators (SPOs) in the network
- Each SPO operates 1 block producer and 2 relay nodes (9,000 total nodes)
- Additional infrastructure for dApps and services (~1,000 nodes)
- Total network nodes: 10,000
- Current monthly rewards: ~48 million ADA
- ADA price assumed at $0.45/ADA

#### Infrastructure Cost Estimates

Using the [Aggregated Total Cost Table](#aggregated-total-cost-table), we
estimate total network infrastructure costs based on an average across providers:

| TxkB/s | Cost per Node (Avg) | Network Cost (10,000 nodes) |
| ------ | ------------------- | --------------------------- |
| 4.5    | ~$75                | $750,000                    |
| 50     | ~$107               | $1,070,000                  |
| 100    | ~$149               | $1,490,000                  |
| 150    | ~$242               | $2,420,000                  |
| 200    | ~$284               | $2,840,000                  |
| 250    | ~$327               | $3,270,000                  |
| 300    | ~$369               | $3,690,000                  |

#### Required Confirmed Throughput for Infrastructure Cost Coverage

| Infrastructure Cost (USD) | Required ADA (at $0.45/ADA) | TPS (Avg Tx) | TxkB/s |
| ------------------------- | --------------------------- | ------------ | ------ |
| $750,000                  | 1,666,667                   | 0.29         | 0.43   |
| $1,080,000                | 2,400,000                   | 0.42         | 0.63   |
| $2,000,000                | 4,444,444                   | 0.78         | 1.17   |
| $2,840,000                | 6,311,111                   | 1.11         | 1.66   |

At 200 TxkB/s, total network infrastructure costs (~$2.84M/month) represent
less than 4% of total fee revenue at that throughput (~$77M ADA × $0.45 ≈
$34.7M/month), demonstrating strong economic viability.

#### Required Throughput for Current Reward Maintenance

To maintain current reward levels (~48 million ADA monthly) through transaction
fees as the Reserve depletes:

| Year | Reserve Depletion | Rewards from Fees (ADA) | Required Tx/s | Required TxkB/s |
| ---- | ----------------- | ----------------------- | ------------- | --------------- |
| 2025 | ~0%               | 0                       | 0             | 0               |
| 2026 | ~13%              | 6,240,000               | 10.9          | 16.4            |
| 2027 | ~24%              | 11,520,000              | 20.1          | 30.2            |
| 2028 | ~34%              | 16,320,000              | 28.5          | 42.8            |
| 2029 | ~43%              | 20,640,000              | 36.1          | 54.1            |
| 2030 | ~50%              | 24,000,000              | 41.9          | 62.9            |

> [!Important]
> By 2029, to compensate for Reserve depletion, the network would need to
> process approximately 36 Tx/s (~54 TxkB/s). This is well within the Leios
> operating range — the protocol comfortably supports up to ~190 Tx/s
> (~288 TxkB/s capacity ceiling) while maintaining decentralization.
