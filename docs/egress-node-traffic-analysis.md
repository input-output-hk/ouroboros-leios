# Egress cost estimation per node

> [!Note]
> **100% filled blocks assumption:**
>
> This analysis assumes **fully utilized block space (filled blocks)** for both Ouroboros Praos and Leios protocols. In practice, block utilization may vary, but this provides a conservative upper bound for egress traffic estimation.

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
RB Headers: 129,600 seconds × 1,024 bytes × 20 peers = 2.65 GiB
RB Bodies: 129,600 seconds × 90,112 bytes × 5 peers = 58.39 GiB
Total: 1.35 TiB

Note: 
- IB traffic dominates due to larger body size (98,304 bytes = 96 KiB)
- EB traffic is minimal due to small body size (32 bytes per reference)
- RB traffic is moderate, similar to Praos block size
```

### Monthly Traffic per Node

| IB/s | IB Headers | IB Bodies | EB Headers | EB Bodies | RB Headers | RB Bodies | Total | vs Praos (A) |
|------|------------|-----------|------------|-----------|------------|-----------|-------|--------------|
| 1    | 15.76 GiB  | 1.27 TiB  | 933.12 MiB | 622.08 MiB| 2.65 GiB   | 58.39 GiB | 1.35 TiB | +1,890% |
| 5    | 78.80 GiB  | 6.37 TiB  | 933.12 MiB | 3.11 GiB  | 2.65 GiB   | 58.39 GiB | 6.51 TiB | +9,495% |
| 10   | 157.59 GiB | 12.74 TiB | 933.12 MiB | 6.22 GiB  | 2.65 GiB   | 58.39 GiB | 12.97 TiB | +19,090% |
| 20   | 315.19 GiB | 25.48 TiB | 933.12 MiB | 12.44 GiB | 2.65 GiB   | 58.39 GiB | 25.87 TiB | +38,180% |
| 30   | 472.78 GiB | 38.22 TiB | 933.12 MiB | 18.66 GiB | 2.65 GiB   | 58.39 GiB | 38.77 TiB | +57,270% |

### Monthly Cost by Cloud Provider ($)

| Provider         | Price/GB | Free Allowance (GB) | 1 IB/s | 5 IB/s | 10 IB/s | 20 IB/s | 30 IB/s | vs Praos (A) |
|------------------|----------|---------------------|---------|---------|----------|----------|----------|--------------|
| Google Cloud     | $0.120   | 0                   | $165.60 | $781.20 | $1,556.40| $3,104.40| $4,652.40| +5,987% |
| Railway          | $0.100   | 0                   | $138.00 | $651.00 | $1,297.00| $2,587.00| $3,877.00| +5,251% |
| AWS              | $0.090   | 100                 | $124.20 | $585.90 | $1,167.30| $2,328.30| $3,489.30| +5,036% |
| Microsoft Azure  | $0.087   | 100                 | $120.06 | $566.37 | $1,128.39| $2,250.69| $3,372.99| +4,864% |
| Alibaba Cloud    | $0.074   | 10                  | $102.12 | $481.74 | $960.18  | $1,914.38| $2,868.58| +4,145% |
| DigitalOcean     | $0.010   | 100–10,000          | $13.80  | $65.10  | $129.70  | $258.70  | $387.70  | +523% |
| Oracle Cloud     | $0.0085  | 10,240              | $11.73  | $55.34  | $110.25  | $219.90  | $329.55  | +477% |
| Linode           | $0.005   | 1,024–20,480        | $6.90   | $32.55  | $64.85   | $129.35  | $193.85  | +264% |
| Hetzner          | $0.00108 | 1,024               | $1.49   | $7.03   | $14.01   | $27.94   | $41.87   | +47% |
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
