# Storage cost estimation per node

> [!Note]
> **100% filled blocks assumption:**
>
> This analysis assumes fully utilized block space for both Ouroboros Praos and Leios protocols, similar to the egress analysis. We'll calculate storage requirements at different IB/s rates.

## Praos Baseline Storage
Current Praos storage requirements per node:
- Block size: 88,908 bytes (87,884 body + 1,024 header)
- Block frequency: 0.05 blocks/slot
- Slots per month: 2,592,000 (30 days * 86,400 slots/day)
- Total blocks: 129,600 (0.05 * 2,592,000)
- Raw storage: 129,600 * 88,908 = 11.52 GiB/month
- Compressed (79%): 2.42 GiB/month

## Leios Storage Components

### Base Parameters

### Block Sizes
- Input Block (IB): 98,304 bytes (96 KiB)
- Endorsement Block (EB): 32 bytes per IB reference
- Ranking Block (RB): 90,112 bytes (88 KiB)
- Average transaction size: 1,400 bytes (from mainnet data)
- Transactions per IB: ~70 (98,304/1,400)

### Time Parameters
- Seconds per month: 2,592,000 (30 days)
- Stage length: 20 slots
- EBs per stage: 1.5
- RBs per stage: 1 (every 20 slots)

## Storage Components

### 1. Ledger State (UTXO Set)
- Base ledger size: 200 GB (current Cardano mainnet)
- Growth rate depends on transaction volume
- Compression ratio: ~79% (based on historical data)

### 2. Chain State (Transaction History)

#### Input Blocks (IB)
- Header: 304 bytes
- Body: 98,304 bytes
- Total per IB: 98,608 bytes

#### Endorsement Blocks (EB)
- Header: 240 bytes
- Body: 32 bytes per IB reference
- Total per EB: 240 + (32 × number of IB references)

#### Votes
- Size: 150 bytes per vote
- Votes per pipeline: 600
- Votes per EB: 900 (600 × 1.5 EBs)

#### Ranking Blocks (RB)
- Header: 1,024 bytes
- Body: 90,112 bytes
- Total per RB: 91,136 bytes

## Monthly Storage Analysis

### Example Calculation (1 IB/s)
```
IB Storage: 2,592,000 seconds × 98,608 bytes = 244.31 GiB
EB Storage: 2,592,000 seconds × (240 + 32) bytes × 1.5 EBs = 1.05 GiB
Vote Storage: 194,400 seconds × 150 bytes × 900 votes = 24.38 GiB
RB Storage: 129,600 seconds × 91,136 bytes = 11.02 GiB
Total Raw: 280.76 GiB
Compressed (79%): 58.96 GiB
```

### Monthly Storage per Node

| IB/s | Chain State Raw | Chain State Compressed (79%) | Ledger State | Total Storage | vs Praos (11.52 GiB) |
|------|----------------|----------------------------|--------------|---------------|---------------------|
| 1    | 280.76 GiB     | 58.96 GiB                  | 200 GiB      | 258.96 GiB    | +2,337%            |
| 5    | 1,359.72 GiB   | 285.54 GiB                 | 200 GiB      | 485.54 GiB    | +4,114%            |
| 10   | 2,708.42 GiB   | 568.77 GiB                 | 200 GiB      | 768.77 GiB    | +6,572%            |
| 20   | 5,405.82 GiB   | 1,135.22 GiB               | 200 GiB      | 1,335.22 GiB  | +11,490%           |
| 30   | 8,103.22 GiB   | 1,701.68 GiB               | 200 GiB      | 1,901.68 GiB  | +16,408%           |

> [!Note]
> - Percentage increases are calculated against uncompressed Praos baseline of 11.52 GiB/month
> - While Leios chain state can potentially be compressed (shown in the "Chain State Compressed" column), current Cardano nodes do not compress chain state
> - Compression ratio of 79% is based on research findings from the technical report using xz -9 compression on historical mainnet data
> - Actual compression ratios may vary for future blocks and transactions

## Cost Analysis

### Monthly Cost by Cloud Provider ($)

| Provider         | Price/GB | Free Allowance (GB) | 1 IB/s (58.96 GB) | 5 IB/s (285.54 GB) | 10 IB/s (568.77 GB) | 20 IB/s (1,135.22 GB) | 30 IB/s (1,701.68 GB) |
|------------------|----------|---------------------|-------------------|--------------------|---------------------|-----------------------|-----------------------|
| Google Cloud     | $0.040   | 0                   | $2.36             | $11.42             | $22.75              | $45.41                | $68.07                |
| Railway          | $0.150   | 0                   | $8.84             | $42.83             | $85.32              | $170.28               | $255.25               |
| AWS              | $0.080   | 100                 | $4.72             | $22.84             | $45.50              | $90.82                | $136.13               |
| Microsoft Azure  | $0.075   | 100                 | $4.42             | $21.42             | $42.66              | $85.14                | $127.63               |
| Alibaba Cloud    | $0.050   | 10                  | $2.95             | $14.28             | $28.44              | $56.76                | $85.08                |
| DigitalOcean     | $0.100   | 100–10,000          | $5.90             | $28.55             | $56.88              | $113.52               | $170.17               |
| Oracle Cloud     | $0.0425  | 10,240              | $2.51             | $12.14             | $24.17              | $48.25                | $72.32                |
| Linode           | $0.100   | 1,024–20,480        | $5.90             | $28.55             | $56.88              | $113.52               | $170.17               |
| Hetzner          | $0.046   | 0                   | $2.71             | $13.13             | $26.16              | $52.22                | $78.28                |
| UpCloud          | $0.056   | 1,024–24,576        | $3.30             | $15.99             | $31.85              | $63.57                | $95.29                |

### Notes
- **Compressed Storage Sizes**: 1 IB/s = 58.96 GB, 5 IB/s = 285.54 GB, 10 IB/s = 568.77 GB, 20 IB/s = 1,135.22 GB, 30 IB/s = 1,701.68 GB
- **Pricing Sources**: Updated from official provider websites as of April 1, 2025 (e.g., Hetzner at $0.046/GB from €0.044/GB at €1 = $1.05)
- **Free Allowances**: Listed for reference but not applied to reduce costs in this table
- **Currency**: All costs in USD, with Hetzner converted from euros using an estimated exchange rate of €1 = $1.05

## Storage Cost Sources

| Provider | Price/GB | Source | Last Updated |
|----------|----------|---------|--------------|
| Google Cloud | $0.040 | https://cloud.google.com/compute/disks-image-pricing | Feb 2025 |
| Railway | $0.150 | https://railway.app/pricing | - |
| AWS | $0.080 | https://aws.amazon.com/ebs/pricing/ | 2023 |
| Microsoft Azure | $0.075 | https://azure.microsoft.com/pricing/details/managed-disks/ | Dec 2024 |
| Alibaba Cloud | $0.050 | https://www.alibabacloud.com/pricing | 2024 |
| DigitalOcean | $0.100 | https://www.digitalocean.com/pricing/ | - |
| Oracle Cloud | $0.0425 | https://www.oracle.com/cloud/pricing/ | Dec 2024 |
| Linode | $0.100 | https://www.linode.com/pricing/ | Apr 2023 |
| Hetzner | $0.046 | https://www.hetzner.com/cloud/pricing | 2024 |
| UpCloud | $0.056 | https://upcloud.com/pricing/ | - |

Note: Prices may vary by region and volume. Some providers offer free tiers or volume discounts not reflected in these base rates. The table shows the standard storage rates for the most commonly used regions.
