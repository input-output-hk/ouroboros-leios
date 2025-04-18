# Leios Node Operating Costs Analysis

## Overview

This document provides a list of cost items that we used for our analysis of the
operational costs associated with running a Leios node. As a baseline
calculation we use Ouroboros Praos for comparisons and different block usage
percentages.

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
different cloud providers based on throughput rates (IB/s).

| Provider         | Cost Item           | 0.05 IB/s   | 1 IB/s      | 5 IB/s        | 10 IB/s       | 20 IB/s       | 30 IB/s       |
| ---------------- | ------------------- | ----------- | ----------- | ------------- | ------------- | ------------- | ------------- |
| **AWS**          | Compute (vCPU)      | $62.05      | $62.05      | $124.10       | $124.10       | $248.20       | $248.20       |
|                  | Compute (RAM)       | $20.79      | $41.59      | $41.59        | $83.18        | $83.18        | $83.18        |
|                  | Storage             | $0.00       | $11.40      | $88.66        | $185.24       | $378.39       | $571.54       |
|                  | Egress              | $0.00       | $108.00     | $535.50       | $1,071.90     | $2,142.00     | $3,212.10     |
|                  | IOPS                | $10.00      | $10.00      | $15.00        | $25.00        | $50.00        | $75.00        |
|                  | **Total (AWS)**     | **$92.84**  | **$233.04** | **$804.85**   | **$1,489.42** | **$2,901.77** | **$4,190.02** |
| **GCP**          | Compute (vCPU)      | $52.34      | $52.34      | $152.35       | $152.35       | $304.78       | $304.78       |
|                  | Compute (RAM)       | $35.95      | $71.91      | $71.91        | $143.81       | $143.81       | $143.81       |
|                  | Storage             | $0.52       | $9.70       | $48.33        | $96.62        | $193.20       | $289.77       |
|                  | Egress              | $10.30      | $141.60     | $714.00       | $1,429.20     | $2,856.00     | $4,282.80     |
|                  | IOPS                | $15.00      | $15.00      | $20.00        | $35.00        | $65.00        | $95.00        |
|                  | **Total (GCP)**     | **$114.11** | **$290.55** | **$1,006.59** | **$1,856.98** | **$3,562.79** | **$5,116.16** |
| **Azure**        | Compute (vCPU)      | $61.76      | $61.76      | $123.37       | $123.37       | $246.74       | $246.74       |
|                  | Compute (RAM)       | $19.50      | $39.00      | $39.00        | $78.00        | $78.00        | $78.00        |
|                  | Storage             | $0.00       | $10.69      | $83.12        | $173.66       | $357.74       | $541.82       |
|                  | Egress              | $0.00       | $104.40     | $518.50       | $1,036.17     | $2,070.60     | $3,105.03     |
|                  | IOPS                | $12.00      | $12.00      | $18.00        | $30.00        | $60.00        | $90.00        |
|                  | **Total (Azure)**   | **$93.26**  | **$227.85** | **$781.99**   | **$1,441.20** | **$2,813.08** | **$4,061.59** |
| **DigitalOcean** | Compute (vCPU)      | $42.00      | $42.00      | $84.00        | $84.00        | $168.00       | $168.00       |
|                  | Compute (RAM)       | $16.28      | $32.56      | $32.56        | $65.12        | $65.12        | $65.12        |
|                  | Storage             | $0.00       | $14.25      | $110.83       | $231.55       | $472.99       | $714.43       |
|                  | Egress              | $0.00       | $11.80      | $59.50        | $119.10       | $238.00       | $356.90       |
|                  | IOPS                | $8.00       | $8.00       | $12.00        | $25.00        | $45.00        | $65.00        |
|                  | **Total (DO)**      | **$66.28**  | **$108.61** | **$298.89**   | **$524.77**   | **$989.11**   | **$1,369.45** |
| **Linode**       | Compute (vCPU)      | $36.00      | $36.00      | $60.00        | $60.00        | $120.00       | $120.00       |
|                  | Compute (RAM)       | $21.75      | $43.51      | $43.51        | $87.02        | $87.02        | $87.02        |
|                  | Storage             | $0.00       | $0.00       | $18.43        | $139.15       | $380.59       | $622.03       |
|                  | Egress              | $0.00       | $5.90       | $29.75        | $59.55        | $119.00       | $178.45       |
|                  | IOPS                | $7.00       | $7.00       | $10.00        | $20.00        | $40.00        | $60.00        |
|                  | **Total (Linode)**  | **$64.75**  | **$92.41**  | **$161.69**   | **$365.72**   | **$746.61**   | **$1,067.50** |
| **Hetzner**      | Compute (vCPU)      | $5.40       | $5.40       | $17.80        | $17.80        | $32.90        | $32.90        |
|                  | Compute (RAM)       | $4.98       | $9.96       | $9.96         | $19.93        | $19.93        | $19.93        |
|                  | Storage             | $0.60       | $11.16      | $55.58        | $111.11       | $222.17       | $333.24       |
|                  | Egress              | $0.00       | $0.00       | $6.43         | $12.87        | $25.70        | $38.54        |
|                  | IOPS                | $5.00       | $5.00       | $8.00         | $15.00        | $30.00        | $45.00        |
|                  | **Total (Hetzner)** | **$15.98**  | **$31.52**  | **$97.77**    | **$176.71**   | **$330.70**   | **$469.61**   |

> [!Note]
> All costs are monthly estimates in USD ($) based on the Input Blocks per
> second (IB/s) rate. Higher throughput configurations are typically dominated
> by egress costs, followed by compute and storage costs. Free tier allowances
> have been factored into calculations where applicable.

> [!Important] 
> Storage costs shown above represent only one month of
> blockchain data. As blockchain history accumulates over time, storage
> requirements and associated costs will continuously increase, particularly for
> higher IB/s rates.

> [!Note] 
> Storage and data transfer use binary prefixes (GiB = 2³⁰ bytes), while
> RAM uses decimal prefixes (GB = 10⁹ bytes), following industry standards for
> cloud computing.

## Cost/ Revenue Analysis

This section analyzes potential revenue from transaction fees based on the current Cardano mainnet fee calculation formula. We examine three scenarios with different transaction sizes to estimate revenue potential.

### Fee Calculation Formula

Cardano calculates transaction fees using the formula:

$$Fee = a + (b \times size)$$

Where:
- $a$ = 155,381 Lovelace (0.155381 ADA) - fixed minimum fee per transaction
- $b$ = 44.0576 Lovelace per byte (0.0000440576 ADA per byte) - fee per byte
- $size$ = transaction size in bytes

### Transaction Size Scenarios

We analyze three transaction size scenarios based on observed Cardano network data:

| Transaction Type            | Size (bytes) | Txs/ Block (TPB) | TPS (Praos)   | Fee/Tx (ADA) |
| --------------------------- | ------------ | ---------------- | ------------- | ------------ |
| **Average** since epoch 500 | 1,400        | ~70              | ~3.5          | 0.217062     |
| **Minimum** size            | 250          | ~393             | ~19.65        | 0.166395     |
| **Maximum** size            | 16,000       | ~6               | ~0.3          | 0.861303     |

> [!Note]
> TPB and TPS calculations assume fully utilized blocks. In practice, utilization varies based on network demand.

### Cost vs Revenue Analysis by IB Rate

To better understand the relationship between operational costs and potential revenue, we can analyze different Input Block (IB) rate scenarios aligned with our transaction types.

#### Throughput Mapping

The following table maps IB/s rates to transactions per second (TPS) for each transaction type:

| IB/s Rate | Average Tx (1,400 bytes) | Minimum Tx (250 bytes) | Maximum Tx (16,000 bytes) |
|-----------|--------------------------|------------------------|---------------------------|
| 0.05      | 3.5 TPS                  | 19.65 TPS              | 0.3 TPS                   |
| 1         | 70 TPS                   | 393 TPS                | 6 TPS                     |
| 5         | 350 TPS                  | 1,965 TPS              | 30 TPS                    |
| 10        | 700 TPS                  | 3,930 TPS              | 60 TPS                    |
| 20        | 1,400 TPS                | 7,860 TPS              | 120 TPS                   |
| 30        | 2,100 TPS                | 11,790 TPS             | 180 TPS                   |

#### Monthly Revenue Projections by IB Rate (ADA)

| IB/s Rate | Average Tx (1,400 bytes)   | Minimum Tx (250 bytes)    | Maximum Tx (16,000 bytes)  |
|-----------|----------------------------|---------------------------|----------------------------|
| 0.05      | 1,969,768.85               | 8,474,945.16              | 669,750.34                 |
| 1         | 39,395,377.00              | 169,498,903.20            | 13,395,006.80              |
| 5         | 196,976,885.00             | 847,494,516.00            | 66,975,034.00              |
| 10        | 393,953,770.00             | 1,694,989,032.00          | 133,950,068.00             |
| 20        | 787,907,540.00             | 3,389,978,064.00          | 267,900,136.00             |
| 30        | 1,181,861,310.00           | 5,084,967,096.00          | 401,850,204.00             |

> [!Important]
> This analysis demonstrates that potential fee revenue at higher IB rates could significantly exceed operational costs for running Leios nodes. However, these calculations assume 100% block utilization and don't account for stake pool operator (SPO) reward sharing, or market dynamics.

> [!Warning]
> The revenue figures above represent **total network revenue**, while cost figures in the [Aggregated Total Cost Table](#aggregated-total-cost-table) represent costs for **individual nodes**. In a decentralized network with approximately 3,000 stake pool operators, each typically running multiple nodes (1 block producer + 2 relays), plus additional relay infrastructure for dApps and services, the total network infrastructure cost would be significantly higher. A proper economic analysis must consider that:
> 
> 1. Each SPO only receives a portion of the total fees, proportional to their stake in the network
> 2. The total network infrastructure cost would be roughly 9,000+ nodes (3,000 SPOs × 3 nodes each, plus additional relay infrastructure)
> 3. Revenue distribution mechanisms and network parameters ultimately determine individual operator profitability

### TPS Breakeven Analysis for Network Infrastructure

To maintain the current network reward structure as the Reserve depletes, we can calculate the required transaction throughput needed to cover the operational costs of all network participants.

Assuming:
- Approximately 3,000 stake pool operators (SPOs) in the network
- Each SPO operates 1 block producer and 2 relay nodes (9,000 total nodes)
- Additional infrastructure for dApps and services (~1,000 nodes)
- Total network nodes: 10,000
- Current monthly rewards: ~48 million ADA

#### Infrastructure Cost Estimates

Using the [Aggregated Total Cost Table](#aggregated-total-cost-table), we can estimate total network infrastructure costs:

| IB/s Rate | Cost per Node (Avg) | Network Cost (10,000 nodes) |
|-----------|---------------------|----------------------------|
| 0.05      | $80 USD             | $800,000 USD               |
| 1         | $200 USD            | $2,000,000 USD             |
| 5         | $700 USD            | $7,000,000 USD             |
| 10        | $1,300 USD          | $13,000,000 USD            |
| 20        | $2,500 USD          | $25,000,000 USD            |
| 30        | $3,600 USD          | $36,000,000 USD            |

#### Required TPS for Infrastructure Cost Coverage

Using average transaction sizes and fees, we can calculate the required TPS to generate enough fees to cover infrastructure costs:

| Infrastructure Cost (USD) | Required ADA (at $0.45/ADA) | TPS (Avg Tx) | TPS (Min Tx) | Equivalent IB/s |
|---------------------------|----------------------------|--------------|--------------|-----------------|
| $800,000                  | 1,777,778                  | 0.31         | 0.40         | 0.004           |
| $2,000,000                | 4,444,444                  | 0.78         | 1.00         | 0.011           |
| $7,000,000                | 15,555,556                 | 2.72         | 3.49         | 0.039           |
| $13,000,000               | 28,888,889                 | 5.05         | 6.48         | 0.072           |
| $25,000,000               | 55,555,556                 | 9.71         | 12.47        | 0.139           |
| $36,000,000               | 80,000,000                 | 13.99        | 17.96        | 0.200           |

#### Required TPS for Current Reward Maintenance

To maintain current reward levels (~48 million ADA monthly) through transaction fees as the Reserve depletes:

| Year | Reserve Depletion | Rewards from Fees (ADA) | Required TPS (Avg Tx) | Required IB/s |
|------|-------------------|-------------------------|----------------------|---------------|
| 2025 | ~0%               | 0                       | 0                    | 0             |
| 2026 | ~13%              | 6,240,000               | 10.9                 | 0.16          |
| 2027 | ~24%              | 11,520,000              | 20.1                 | 0.29          |
| 2028 | ~34%              | 16,320,000              | 28.5                 | 0.41          |
| 2029 | ~43%              | 20,640,000              | 36.1                 | 0.52          |
| 2030 | ~50%              | 24,000,000              | 41.9                 | 0.60          |

> [!Important]
> By 2029, to compensate for Reserve depletion, the network would need to process approximately 36 TPS with average-sized transactions, requiring an Input Block rate of around 0.52 IB/s - roughly 10 times the current mainnet throughput. Leios' design would comfortably support this increased throughput while maintaining decentralization.
