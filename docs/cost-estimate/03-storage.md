# Storage cost estimation per node

> [!Note]
> **100% filled blocks assumption:**
>
> This analysis assumes fully utilized block space for both Ouroboros Praos and Leios protocols, similar to the egress analysis. We'll calculate storage requirements at different IB/s rates.
>
> **Compression note:**
> While early experiments show that >70% compression is feasible on mainnet data, this analysis does not include compression benefits. The calculations represent raw storage requirements without compression.

## Ouroboros Praos

We start with Ouroboros Praos to establish a baseline for storage requirements. In Praos, storage is primarily used for maintaining the blockchain history.

### Block Components

| Component      | Size (bytes) | Size (KiB) |
|----------------|--------------|------------|
| Block header   | 1,024        | 1          |
| Block body     | 90,112       | 88         |
| **Total block**| **91,136**   | **89**     |

### Block Production Rate

| Parameter               | Value                  | Formula                     |
|-------------------------|------------------------|----------------------------|
| Slot duration           | 1 second               | Protocol parameter          |
| Active slot coefficient | 0.05                   | Protocol parameter          |
| **Blocks per second**   | **0.05**               | $$1 \times 0.05$$           |

### Monthly Storage Formula

$$S_{monthly} = B_{size} \times R_{block} \times T_{month}$$

where:
- $S_{monthly}$ = Monthly storage requirement in bytes
- $B_{size}$ = Size of each block in bytes
- $R_{block}$ = Block production rate (blocks per second)
- $T_{month}$ = Number of seconds in a month (30.4167 days = 2,628,000 seconds)

### Monthly Storage Calculation

$$S_{monthly} = 91,136 \times 0.05 \times 2,628,000$$
$$S_{monthly} = 11,973,196,800 \text{ bytes} \approx 11.97 \text{ GiB}$$

### Ledger State
In addition to the blockchain history, nodes must maintain:
- Current approximate size: 200 GiB (as of April 2025)
- Growth rate depends on transaction volume

## Ouroboros Leios

Leios introduces multiple block types that contribute to the overall storage requirements.

### Block Size Components

| Component                     | Size (bytes) | Size (KiB) |
|-------------------------------|--------------|------------|
| Input Block (IB) Header       | 304          | 0.3        |
| Input Block (IB) Body         | 98,304       | 96         |
| **Total IB**                  | **98,608**   | **96.3**   |
| Endorsement Block (EB) Header | 240          | 0.2        |
| EB Body (per IB reference)    | 32           | 0.03       |
| Ranking Block (RB) Header     | 1,024        | 1          |
| Ranking Block (RB) Certificate| 7,168        | 7          |
| **Total RB**                  | **8,192**    | **8**      |

> [!NOTE]
> The RB body in Leios contains exactly one certificate of size 7,168 bytes, not the full 88 KiB as in Praos blocks.

### Time and Rate Parameters

| Parameter           | Value                  | Formula/Source                |
|---------------------|------------------------|-------------------------------|
| Stage length        | 20 slots (20 seconds)  | Protocol parameter            |
| EBs per stage       | 1.5                    | Protocol parameter            |
| Votes per EB        | 600                    | Protocol parameter            |
| RBs per stage       | 1                      | Protocol parameter            |
| Days per month      | 30.4167                | $$\frac{365}{12}$$            |
| Seconds per month   | 2,628,000              | $$30.4167 \times 24 \times 60 \times 60$$ |
| Stages per month    | 131,400                | $$\frac{2,628,000}{20}$$      |

> [!Note]
> Votes are ephemeral and don't require permanent storage, so they are excluded from the storage calculations.

### Storage Formulas

1. **IB Storage**:
   $$S_{IB} = R_{IB} \times T_{month} \times Size_{IB}$$
   where:
   - $R_{IB}$ = Input Block rate (IB/s)
   - $T_{month}$ = Number of seconds in a month (2,628,000)
   - $Size_{IB}$ = Size of each IB in bytes (98,608)

2. **EB Storage**:
   $$S_{EB} = N_{EB\_stage} \times N_{stages} \times (Size_{EB\_header} + Size_{EB\_body} \times N_{IB\_refs})$$
   where:
   - $N_{EB\_stage}$ = Number of EBs per stage (1.5)
   - $N_{stages}$ = Number of stages per month (131,400)
   - $Size_{EB\_header}$ = EB header size (240 bytes)
   - $Size_{EB\_body}$ = EB body size per reference (32 bytes)
   - $N_{IB\_refs}$ = Number of IB references per EB (varies by IB rate)

3. **RB Storage**:
   $$S_{RB} = N_{RB\_stage} \times N_{stages} \times Size_{RB}$$
   where:
   - $N_{RB\_stage}$ = Number of RBs per stage (1)
   - $N_{stages}$ = Number of stages per month (131,400)
   - $Size_{RB}$ = Size of each RB (8,192 bytes = header + certificate)

4. **Total Chain State Storage**:
   $$S_{total} = S_{IB} + S_{EB} + S_{RB}$$

### Storage Calculation (0.05 IB/s)

For a fair comparison, we calculate Leios storage at the same transaction throughput as Praos (0.05 blocks or IBs per second):

1. **IB Storage**:
   $$S_{IB} = 0.05 \times 2,628,000 \times 98,608 = 12,957,091,200 \text{ bytes} \approx 12.39 \text{ GiB}$$

2. **EB Storage**:
   At 0.05 IB/s and 20-second stages, each EB contains references to approximately 1 IB:
   $$S_{EB} = 1.5 \times 131,400 \times (240 + 32 \times 1) = 1,065,744,000 \text{ bytes} \approx 1.02 \text{ GiB}$$

3. **RB Storage**:
   $$S_{RB} = 1 \times 131,400 \times 8,192 = 1,076,428,800 \text{ bytes} \approx 1.00 \text{ GiB}$$

4. **Total Storage**:
   $$S_{total} = 12.39 + 1.02 + 1.00 = 14.41 \text{ GiB}$$

### Storage Component Analysis (at 0.05 IB/s)

| Component | Storage Size | % of Total Chain State |
|-----------|--------------|------------------------|
| IB        | 12.39 GiB    | 86.0%                  |
| EB        | 1.02 GiB     | 7.1%                   |
| RB        | 1.00 GiB     | 6.9%                   |

At the baseline rate, Input Blocks dominate the storage requirements (86.0%), with Endorsement Blocks and Ranking Blocks contributing similar smaller portions.

### Monthly Storage at Higher IB Rates

| IB/s | IB Storage | EB Storage | RB Storage | Total Storage | vs Praos |
|------|------------|------------|------------|---------------|----------|
| 0.05 | 12.39 GiB  | 1.02 GiB   | 1.00 GiB   | 14.41 GiB     | +20%     |
| 1    | 247.70 GiB | 1.07 GiB   | 1.00 GiB   | 249.77 GiB    | +1,987%  |
| 5    | 1,238.50 GiB | 1.27 GiB | 1.00 GiB   | 1,240.77 GiB  | +10,266% |
| 10   | 2,477.00 GiB | 1.52 GiB | 1.00 GiB   | 2,479.52 GiB  | +20,615% |
| 20   | 4,954.00 GiB | 2.01 GiB | 1.00 GiB   | 4,957.01 GiB  | +41,312% |
| 30   | 7,431.00 GiB | 2.51 GiB | 1.00 GiB   | 7,434.51 GiB  | +62,009% |

> [!Note]
> - Percentage increases are calculated against Praos baseline of 11.97 GiB/month
> - EB sizes vary slightly with IB/s rates as they contain references to IBs
> - While Leios chain state could potentially be compressed by >70% based on early experiments, this analysis uses raw storage requirements
> - Current Cardano nodes do not compress chain history, so we focus on uncompressed values for practical deployment considerations

### Storage Component Analysis at Higher IB Rates

As the IB rate increases, the storage profile changes dramatically:

| IB/s | IB Storage % | EB Storage % | RB Storage % |
|------|--------------|--------------|--------------|
| 0.05 | 86.0%        | 7.1%         | 6.9%         |
| 1    | 99.2%        | 0.4%         | 0.4%         |
| 5    | 99.8%        | 0.1%         | 0.1%         |
| 10   | 99.9%        | 0.1%         | <0.1%        |
| 20   | 99.9%        | <0.1%        | <0.1%        |
| 30   | >99.9%       | <0.1%        | <0.1%        |

This shows that as throughput increases, Input Block storage completely dominates the requirements, comprising over 99% of storage at rates above 1 IB/s.

## Cost Analysis

### Monthly Storage Cost by Cloud Provider ($)

| Provider         | Price/GB | Free Allowance (GB) | 0.05 IB/s | 1 IB/s | 5 IB/s | 10 IB/s | 20 IB/s | 30 IB/s |
|------------------|----------|---------------------|-----------|--------|---------|---------|---------|---------|
| Google Cloud     | $0.040   | 0                   | $0.58     | $9.99  | $49.63  | $99.18  | $198.28 | $297.38 |
| Railway          | $0.150   | 0                   | $2.16     | $37.47 | $186.12 | $371.93 | $743.55 | $1,115.18 |
| AWS              | $0.080   | 100                 | $0.00     | $12.00 | $91.26  | $190.36 | $388.56 | $586.76 |
| Microsoft Azure  | $0.075   | 100                 | $0.00     | $11.23 | $85.56  | $178.46 | $366.28 | $554.09 |
| Alibaba Cloud    | $0.050   | 10                  | $0.22     | $12.00 | $61.54  | $123.48 | $247.61 | $371.73 |
| DigitalOcean     | $0.100   | 100                 | $0.00     | $15.00 | $114.08 | $237.95 | $485.70 | $733.45 |
| Oracle Cloud     | $0.0425  | 10,240              | $0.00     | $0.00  | $0.00   | $0.00   | $0.00   | $0.00   |
| Linode           | $0.100   | 1,024               | $0.00     | $0.00  | $21.68  | $145.55 | $393.30 | $641.05 |
| Hetzner          | $0.046   | 0                   | $0.66     | $11.49 | $57.07  | $114.06 | $228.02 | $342.00 |
| UpCloud          | $0.056   | 1,024               | $0.00     | $0.00  | $12.15  | $81.56  | $219.83 | $358.15 |

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
