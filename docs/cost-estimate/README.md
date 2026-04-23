# Leios Node Operating Costs Analysis

## Overview

This document provides a list of cost items used for our analysis of the
operational costs associated with running a Leios node. As a baseline we use
Ouroboros Praos for comparisons. All cost estimates are for **Linear Leios
(CIP-164)** and assume fully confirmed transaction throughput (TxkB/s —
transaction kilobytes per second reaching the ledger). Costs represent
conservative upper bounds: 600 votes per EB (wFA+LS committee), individual
BLS vote verification, and 100% confirmed block utilization. CPU costs use
**mainnet-average demand** (including organic Plutus usage as measured on
Cardano mainnet); Plutus-heavy workloads will cost more.

The primary throughput metric is **confirmed TxkB/s**, derived from the
CIP-164 design where:
- EBs reference transactions by 32-byte hash at 0.05 EB/s
- Transactions are gossiped via the mempool (not bundled in IBs)
- $P(\text{EB certified}) \approx 0.48$ sets the capacity ceiling at ~288 TxkB/s

### Leios at Praos-equivalent load

At confirmed throughput at or below the Praos capacity ceiling (4.5 TxkB/s),
Linear Leios processes the same transaction volume and incurs the same
per-transaction Apply cost. The difference is fixed protocol overhead —
vote validation, certificate validation, and the EB/RB gossip machinery — which
is present regardless of throughput. At near-Praos load this overhead dominates;
as throughput grows toward ~288 TxkB/s it is amortized over more confirmed
transactions and the cost per TxkB/s converges.

The **4.5 (Praos)** column in the tables below shows actual Praos protocol costs
(no EB/vote/cert overhead). The **5 TxkB/s** column is the Leios baseline: just
above Praos-equivalent load, where the fixed overhead is fully visible. Note that
Praos requires ~16 GB RAM (in-memory UTxO) while Leios uses only ~4 GB RAM
(UTxO-HD moves the UTxO set to disk), which partially offsets the fixed overhead
cost at all throughput levels.

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
different cloud providers based on confirmed throughput in TxkB/s. The
**4.5 (Praos)** column uses actual Praos protocol costs including 16 GB RAM
(in-memory UTxO). All Leios columns use 4 GB RAM (UTxO-HD).

| Provider         | Cost Item           | 4.5 (Praos) | 5 TxkB/s    | 50 TxkB/s   | 100 TxkB/s  | 200 TxkB/s  | 300 TxkB/s  |
|------------------|---------------------|-------------|-------------|-------------|-------------|-------------|-------------|
| **AWS**          | Compute (vCPU)      | $62.05      | $62.05      | $62.05      | $62.05      | $62.05      | $62.05      |
|                  | Compute (RAM)       | $83.18      | $20.79      | $20.79      | $20.79      | $20.79      | $20.79      |
|                  | Storage             | $0.00       | $0.00       | $2.71       | $13.34      | $34.58      | $55.83      |
|                  | Egress              | $0.00       | $0.00       | $52.36      | $112.03     | $231.35     | $350.68     |
|                  | IOPS                | $10.00      | $10.00      | $10.00      | $10.00      | $10.00      | $10.00      |
|                  | **Total (AWS)**     | **$155.23** | **$92.84**  | **$147.91** | **$218.21** | **$358.77** | **$499.35** |
| **GCP**          | Compute (vCPU)      | $52.34      | $52.34      | $52.34      | $52.34      | $52.34      | $52.34      |
|                  | Compute (RAM)       | $143.82     | $35.95      | $35.95      | $35.95      | $35.95      | $35.95      |
|                  | Storage             | $0.47       | $0.59       | $5.36       | $10.67      | $21.29      | $31.92      |
|                  | Egress              | $7.49       | $10.21      | $81.82      | $161.37     | $320.47     | $479.57     |
|                  | IOPS                | $15.00      | $15.00      | $15.00      | $15.00      | $15.00      | $15.00      |
|                  | **Total (GCP)**     | **$219.12** | **$114.09** | **$190.47** | **$275.33** | **$445.05** | **$614.78** |
| **Azure**        | Compute (vCPU)      | $61.76      | $61.76      | $61.76      | $61.76      | $61.76      | $61.76      |
|                  | Compute (RAM)       | $78.00      | $19.50      | $19.50      | $19.50      | $19.50      | $19.50      |
|                  | Storage             | $0.00       | $0.00       | $2.54       | $12.50      | $32.42      | $52.34      |
|                  | Egress              | $0.00       | $0.00       | $50.62      | $108.29     | $223.64     | $338.99     |
|                  | IOPS                | $12.00      | $12.00      | $12.00      | $12.00      | $12.00      | $12.00      |
|                  | **Total (Azure)**   | **$151.76** | **$93.26**  | **$146.42** | **$214.05** | **$349.32** | **$484.59** |
| **DigitalOcean** | Compute (vCPU)      | $42.00      | $42.00      | $42.00      | $42.00      | $42.00      | $42.00      |
|                  | Compute (RAM)       | $65.12      | $16.28      | $16.28      | $16.28      | $16.28      | $16.28      |
|                  | Storage             | $0.00       | $0.00       | $3.39       | $16.67      | $43.22      | $69.79      |
|                  | Egress              | $0.00       | $0.00       | $0.00       | $3.45       | $16.71      | $29.96      |
|                  | IOPS                | $8.00       | $8.00       | $8.00       | $8.00       | $8.00       | $8.00       |
|                  | **Total (DO)**      | **$115.12** | **$66.28**  | **$69.67**  | **$86.40**  | **$126.21** | **$166.03** |
| **Linode**       | Compute (vCPU)      | $36.00      | $36.00      | $36.00      | $36.00      | $36.00      | $36.00      |
|                  | Compute (RAM)       | $87.02      | $21.75      | $21.75      | $21.75      | $21.75      | $21.75      |
|                  | Storage             | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       | $0.00       |
|                  | Egress              | $0.00       | $0.00       | $0.00       | $1.60       | $8.23       | $14.86      |
|                  | IOPS                | $7.00       | $7.00       | $7.00       | $7.00       | $7.00       | $7.00       |
|                  | **Total (Linode)**  | **$130.02** | **$64.75**  | **$64.75**  | **$66.35**  | **$72.98**  | **$79.61**  |
| **Hetzner**      | Compute (vCPU)      | $6.59       | $6.59       | $6.59       | $6.59       | $6.59       | $6.59       |
|                  | Compute (RAM)       | $12.42      | $4.39       | $4.39       | $4.39       | $4.39       | $4.39       |
|                  | Storage             | $0.74       | $0.92       | $8.44       | $16.80      | $33.53      | $50.26      |
|                  | Egress              | $0.00       | $0.00       | $0.00       | $0.35       | $1.81       | $3.27       |
|                  | IOPS                | $5.00       | $5.00       | $5.00       | $5.00       | $5.00       | $5.00       |
|                  | **Total (Hetzner)** | **$24.75**  | **$16.90**  | **$24.42**  | **$33.13**  | **$51.32**  | **$69.51**  |

> [!Note]
> All costs are monthly estimates in USD ($) based on confirmed throughput in
> TxkB/s (transaction kilobytes per second reaching the ledger).
>
> - **4.5 (Praos)**: Praos protocol at its natural operating point —
>   no EB/vote/cert overhead, but requires ~16 GB RAM for the in-memory UTxO set
> - **5 TxkB/s**: Leios baseline just above Praos capacity; fixed protocol
>   overhead (votes, certs) is fully visible but only ~11% more throughput
>   than Praos — the economic case for Leios emerges at higher throughput
> - Leios columns use the 4 GB RAM tier (UTxO-HD); Praos RAM costs ~4× more
> - Compute (vCPU) uses the 2-core tier for all Leios rows; 4 cores recommended
>   for production headroom (see [01-compute-cpu.md](./01-compute-cpu.md))
> - At higher throughput, egress dominates for premium cloud providers;
>   budget providers (Hetzner, Linode) remain affordable due to generous
>   included transfer
> - Fixed vote overhead (600 votes × 164 B × 0.05 EB/s) contributes ~12 GiB/month
>   in egress regardless of confirmed throughput

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

| TxkB/s        | Tx/s (1,500 B avg) | Monthly Txs     | Fee/Tx (ADA) | Monthly Revenue (ADA) |
| ------------- | ------------------ | --------------- | ------------ | --------------------- |
| 4.5 (Praos)   | 3                  | 7,884,000       | 0.221467     | 1,745,932             |
| 5             | 3                  | 8,760,000       | 0.221467     | 1,940,051             |
| 50            | 33                 | 86,724,000      | 0.221467     | 19,205,255            |
| 100           | 67                 | 176,076,000     | 0.221467     | 38,991,426            |
| 200           | 133                | 349,524,000     | 0.221467     | 77,411,397            |
| 300           | 200                | 525,600,000     | 0.221467     | 116,402,822           |

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
estimate total network infrastructure costs based on an average across providers.
Note that Leios infrastructure is cheaper than Praos at all throughput levels
because UTxO-HD reduces RAM from ~16 GB to ~4 GB per node.

| TxkB/s        | Cost per Node (Avg) | Network Cost (10,000 nodes) |
| ------------- | ------------------- | --------------------------- |
| 4.5 (Praos)   | ~$133               | $1,330,000                  |
| 5 (Leios)     | ~$75                | $750,000                    |
| 50            | ~$107               | $1,070,000                  |
| 100           | ~$149               | $1,490,000                  |
| 200           | ~$234               | $2,340,000                  |
| 300           | ~$319               | $3,190,000                  |

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
