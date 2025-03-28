# Egress cost estimation per node

> [!Note]
> **100% filled blocks assumption:**
>
> This analysis assumes fully utilized block space (filled blocks) for both Ouroboros Praos and Leios protocols. In practice, block utilization may vary, but this provides a conservative upper bound for egress traffic estimation. Transaction sizes are based on mainnet data from Epoch 500 onwards, where average transaction size is ~1,400 bytes.

## Ouroboros Praos

### Back of envelope calculation

#### Blocks/ month
- epoch length 5 days (432,000 slots)
- active slot coefficient 0.05
- yielding 21,600 blocks per epoch
- ~6.0833 epochs per month (365/5/12)
- **131,400 blocks per month**

#### Total block data
- block size 90,112 bytes (88 KiB)
- average transaction size: 1,400 bytes (based on mainnet data)
- average transactions per block: ~13.5 (based on mainnet data)
- **131,400 blocks x 90,112 bytes = 11,840,724,480 bytes ~11.84 GiB**

> [!Note]
>
> For reference, during epoch 500, blocks had an average size of 18.9 KiB
> which is ~21.5% of what's available.

#### Egress traffic for p2p block propagation
- Peers (P): assume:
```
    (A) 20 peers from TargetNumberOfActivePeers default configuration
    (B) ~35 downstream peers per node
```
- Block header size: 1,024 bytes (1 KiB)
- Block body size: 90,112 bytes (88 KiB)
- Propagation model: 100% header propagation, 25% body requests

#### Node traffic
```
(A) Headers: 131,400 blocks x 1,024 bytes x 20 peers = 2.69 GiB
    Bodies: 131,400 blocks x 90,112 bytes x 5 peers = 59.19 GiB
    Total: 61.88 GiB

(B) Headers: 131,400 blocks x 1,024 bytes x 35 peers = 4.71 GiB
    Bodies: 131,400 blocks x 90,112 bytes x 9 peers = 106.55 GiB
    Total: 111.26 GiB
```

- additional traffic from transactions (5-10 GiB?) and consensus (~1-2 GiB?)

#### Final total egress per month/ node
```
(A) Low end: 61.88 GiB + 5 GiB + 1 GiB = 67.88 GiB
    High end: 61.88 GiB + 10 GiB + 2 GiB = 73.88 GiB

(B) Low end: 111.26 GiB + 5 GiB + 1 GiB = 117.26 GiB
    High end: 111.26 GiB + 10 GiB + 2 GiB = 123.26 GiB
```

## Ouroboros Leios

### Block Size Breakdown

#### Input Blocks (IB)
- Header: 304 bytes
  - ProducerId: 32 bytes
  - SlotNo: 64 bytes
  - VRF proof: 80 bytes
  - Body hash: 32 bytes
  - RB Ref: 32 bytes
  - Signature: 64 bytes
- Body: 98,304 bytes

#### Endorsement Blocks (EB)
- Header: 240 bytes
  - ProducerId: 32 bytes
  - SlotNo: 64 bytes
  - VRF proof: 80 bytes
  - Signature: 64 bytes
- Body: 32 bytes per IB reference

#### Votes
- Size: 150 bytes per vote
- Votes per pipeline: 600
- Votes per EB: 600 votes × 1.5 EBs = 900 votes per stage

#### Ranking Blocks (RB)
- Header: 1,024 bytes
- Body: 90,112 bytes

### Monthly Traffic Calculation

#### Base Parameters
- Seconds per month: 2,592,000 (30 days)
- Stage length: 20 slots
- EBs per stage: 1.5
- RBs per stage: 1 (every 20 slots)

#### Example Calculation (1 IB/s, 20 peers, 100% header propagation, 25% body requests)
```
IB Headers: 2,592,000 seconds × 304 bytes × 20 peers = 15.76 GiB
IB Bodies: 2,592,000 seconds × 98,304 bytes × 5 peers = 1.27 TiB
EB Headers: 194,400 seconds × 240 bytes × 20 peers = 933.12 MiB
EB Bodies: 194,400 seconds × 32 bytes × 20 IBs per stage × 5 peers = 622.08 MiB
Votes: 194,400 seconds × 150 bytes × 900 votes × 20 peers = 524.88 GiB
RB Headers: 129,600 seconds × 1,024 bytes × 20 peers = 2.65 GiB
RB Bodies: 129,600 seconds × 90,112 bytes × 5 peers = 58.39 GiB
Total: 1.88 TiB

Note: 
- IB traffic dominates due to larger body size (98,304 bytes = 96 KiB)
- EB traffic is minimal due to small body size (32 bytes per reference)
- Vote traffic is significant due to high volume (900 votes per stage)
- RB traffic is moderate, similar to Praos block size
```

### Monthly Traffic per Node

| IB/s | IB Headers | IB Bodies | EB Headers | EB Bodies | Votes | RB Headers | RB Bodies | Total | vs Praos (A) |
|------|------------|-----------|------------|-----------|-------|------------|-----------|-------|--------------|
| 1    | 15.76 GB   | 1.27 TB   | 933.12 MB  | 622.08 MB | 524.88 GB | 2.65 GB    | 58.39 GB  | 1.88 TB | +2,670% |
| 5    | 78.80 GB   | 6.37 TB   | 933.12 MB  | 3.11 GB   | 2.62 TB   | 2.65 GB    | 58.39 GB  | 9.07 TB | +13,260% |
| 10   | 157.59 GB  | 12.74 TB  | 933.12 MB  | 6.22 GB   | 5.25 TB   | 2.65 GB    | 58.39 GB  | 18.11 TB | +26,590% |
| 20   | 315.19 GB  | 25.48 TB  | 933.12 MB  | 12.44 GB  | 10.50 TB  | 2.65 GB    | 58.39 GB  | 36.19 TB | +53,130% |
| 30   | 472.78 GB  | 38.22 TB  | 933.12 MB  | 18.66 GB  | 15.75 TB  | 2.65 GB    | 58.39 GB  | 54.28 TB | +79,670% |

### Monthly Cost by Cloud Provider ($)

| Provider         | Price/GB | Free Allowance (GB) | 1 IB/s | 5 IB/s | 10 IB/s | 20 IB/s | 30 IB/s | vs Praos (A) |
|------------------|----------|---------------------|---------|---------|----------|----------|----------|--------------|
| Google Cloud     | $0.120   | 0                   | $230.40 | $1,088.40| $2,167.20| $4,325.40| $6,483.60| +8,340% |
| Railway          | $0.100   | 0                   | $192.00 | $907.00 | $1,806.00| $3,604.00| $5,403.00| +7,000% |
| AWS              | $0.090   | 100                 | $172.80 | $816.30 | $1,625.40| $3,243.60| $4,862.70| +6,300% |
| Microsoft Azure  | $0.087   | 100                 | $167.04 | $788.73 | $1,570.89| $3,135.09| $4,699.29| +6,084% |
| Alibaba Cloud    | $0.074   | 10                  | $142.08 | $670.74 | $1,335.78| $2,665.38| $3,995.08| +5,170% |
| DigitalOcean     | $0.010   | 100–10,000          | $19.20  | $90.70  | $180.60  | $360.40  | $540.30  | +699% |
| Oracle Cloud     | $0.0085  | 10,240              | $16.32  | $77.09  | $153.51  | $306.34  | $459.26  | +594% |
| Linode           | $0.005   | 1,024–20,480        | $9.60   | $45.35  | $90.30   | $180.20  | $270.15  | +350% |
| Hetzner          | $0.00108 | 1,024               | $2.07   | $9.80   | $19.50   | $38.92   | $58.35   | +75% |
| UpCloud          | $0.000   | 1,024–24,576        | $0.00   | $0.00   | $0.00    | $0.00    | $0.00    | 0% |

Note: Percentage increases are calculated against Praos scenario A (20 peers) baseline of 67.88 GiB/month and $7.73/month (using average cost across providers)

### Data Egress Cost Sources

| Provider | Price/GB | Source | Last Updated |
|----------|----------|---------|--------------|
| Google Cloud | $0.120 | https://cloud.google.com/vpc/pricing | Feb 2025 |
| Railway | $0.100 | https://railway.app/pricing | - |
| AWS | $0.090 | https://aws.amazon.com/ec2/pricing/ | 2023 |
| Microsoft Azure | $0.087 | https://azure.microsoft.com/pricing/details/bandwidth/ | Dec 2024 |
| Alibaba Cloud | $0.074 | https://www.alibabacloud.com/pricing | 2024 |
| DigitalOcean | $0.010 | https://www.digitalocean.com/pricing/ | - |
| Oracle Cloud | $0.0085 | https://www.oracle.com/cloud/pricing/ | Dec 2024 |
| Linode | $0.005 | https://www.linode.com/pricing/ | Apr 2023 |
| Hetzner | $0.00108 | https://www.hetzner.com/cloud/pricing | 2024 |
| UpCloud | $0.000 | https://upcloud.com/pricing/ | - |

Note: Prices may vary by region and volume. Some providers offer free tiers or volume discounts not reflected in these base rates. The table shows the standard outbound data transfer rates for the most commonly used regions.
