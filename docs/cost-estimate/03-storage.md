# Storage cost estimation per node

> [!Note] 
> 
> **100% filled blocks assumption:**
>
> This analysis assumes fully utilized block space for both Ouroboros Praos and
> Leios protocols, similar to the egress analysis. We'll calculate storage
> requirements at different IB/s rates.
>
> **Compression note:** While early experiments show that >70% compression is
> feasible on mainnet data, this analysis does not include compression benefits.
> The calculations represent raw storage requirements without compression.

## Ouroboros Praos

We start with Ouroboros Praos to establish a baseline for storage requirements.
In Praos, storage is primarily used for maintaining the blockchain history.

### Block Components

| Component       | Size (bytes) | Size (KiB) |
| --------------- | ------------ | ---------- |
| Block header    | 1,024        | 1          |
| Block body      | 90,112       | 88         |
| **Total block** | **91,136**   | **89**     |

### Block Production Rate

| Parameter               | Value    | Formula            |
| ----------------------- | -------- | ------------------ |
| Slot duration           | 1 second | Protocol parameter |
| Active slot coefficient | 0.05     | Protocol parameter |
| **Blocks per second**   | **0.05** | $$1 \times 0.05$$  |

### Monthly Storage Formula

$$S_{monthly} = B_{size} \times R_{block} \times T_{month}$$

where:

- $S_{monthly}$ = Monthly storage requirement in bytes
- $B_{size}$ = Size of each block in bytes
- $R_{block}$ = Block production rate (blocks per second)
- $T_{month}$ = Number of seconds in a month (30.4167 days = 2,628,000 seconds)

### Monthly Storage Calculation

$$S_{monthly} = 91,136 \times 0.05 \times 2,628,000$$

$$S_{monthly} = 11,973,196,800 \text{ bytes} \approx 11.15 \text{ GiB}$$

### Ledger State

In addition to the blockchain history, nodes must maintain:

- Current approximate size: 200 GiB (as of April 2025)
- Growth rate depends on transaction volume

## Ouroboros Leios

Leios introduces multiple block types that contribute to the overall storage
requirements.

### Block Size Components

| Component                      | Size (bytes) | Size (KiB) |
| ------------------------------ | ------------ | ---------- |
| Input Block (IB) Header        | 304          | 0.3        |
| Input Block (IB) Body          | 98,304       | 96         |
| **Total IB**                   | **98,608**   | **96.3**   |
| Endorsement Block (EB) Header  | 240          | 0.2        |
| EB Body (per IB reference)     | 32           | 0.03       |
| Ranking Block (RB) Header      | 1,024        | 1          |
| Ranking Block (RB) Certificate | 7,168        | 7          |
| **Total RB**                   | **8,192**    | **8**      |

> [!NOTE]
> The RB body in Leios contains exactly one certificate of size 7,168 bytes, not
> the full 88 KiB as in Praos blocks.

### Time and Rate Parameters

| Parameter         | Value                 | Formula/Source                            |
| ----------------- | --------------------- | ----------------------------------------- |
| Stage length      | 20 slots (20 seconds) | Protocol parameter                        |
| EBs per stage     | 1.5                   | Protocol parameter                        |
| Votes per EB      | 600                   | Protocol parameter                        |
| RBs per stage     | 1                     | Protocol parameter                        |
| Days per month    | 30.4167               | $$\frac{365}{12}$$                        |
| Seconds per month | 2,628,000             | $$30.4167 \times 24 \times 60 \times 60$$ |
| Stages per month  | 131,400               | $$\frac{2,628,000}{20}$$                  |

> [!Note]
> Votes are ephemeral and don't require permanent storage, so they are
> excluded from the storage calculations.

### Storage Formulas

1. **IB Storage**: $$S_{IB} = R_{IB} \times T_{month} \times Size_{IB}$$
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

3. **RB Storage**: $$S_{RB} = N_{RB\_stage} \times N_{stages} \times Size_{RB}$$
   where:
   - $N_{RB\_stage}$ = Number of RBs per stage (1)
   - $N_{stages}$ = Number of stages per month (131,400)
   - $Size_{RB}$ = Size of each RB (8,192 bytes = header + certificate)

4. **Total Chain State Storage**: $$S_{total} = S_{IB} + S_{EB} + S_{RB}$$

### Storage Calculation (0.05 IB/s)

For a fair comparison, we calculate Leios storage at the same transaction
throughput as Praos (0.05 blocks or IBs per second):

1. **IB Storage**:
   $$S_{IB} = 0.05 \times 2,628,000 \times 98,608 = 12,957,091,200 \text{ bytes} \approx 12.07 \text{ GiB}$$

2. **EB Storage**: At 0.05 IB/s and 20-second stages, each EB contains
   references to approximately 1 IB:
   $$S_{EB} = 1.5 \times 131,400 \times (240 + 32 \times 1) = 53,690,400 \text{ bytes} \approx 0.05 \text{ GiB}$$

3. **RB Storage**:
   $$S_{RB} = 1 \times 131,400 \times 8,192 = 1,076,428,800 \text{ bytes} \approx 1.00 \text{ GiB}$$

4. **Total Storage**: $$S_{total} = 12.07 + 0.05 + 1.00 = 13.12 \text{ GiB}$$

### Storage Component Analysis (at 0.05 IB/s)

| Component | Storage Size | % of Total Chain State |
| --------- | ------------ | ---------------------- |
| IB        | 12.07 GiB    | 92.0%                  |
| EB        | 0.05 GiB     | 0.4%                   |
| RB        | 1.00 GiB     | 7.6%                   |

At the baseline rate, Input Blocks dominate the storage requirements (92.0%),
with Ranking Blocks contributing a smaller portion, and Endorsement Blocks
having minimal impact.

### Monthly Storage at Higher IB Rates

| IB/s | IB Storage   | EB Storage | RB Storage | Total Storage | vs Praos |
| ---- | ------------ | ---------- | ---------- | ------------- | -------- |
| 0.05 | 12.07 GiB    | 0.05 GiB   | 1.00 GiB   | 13.12 GiB     | +18%     |
| 1    | 241.40 GiB   | 0.10 GiB   | 1.00 GiB   | 242.50 GiB    | +2,075%  |
| 5    | 1,207.01 GiB | 0.25 GiB   | 1.00 GiB   | 1,208.26 GiB  | +10,737% |
| 10   | 2,414.02 GiB | 0.45 GiB   | 1.00 GiB   | 2,415.47 GiB  | +21,563% |
| 20   | 4,828.04 GiB | 0.85 GiB   | 1.00 GiB   | 4,829.89 GiB  | +43,217% |
| 30   | 7,242.06 GiB | 1.25 GiB   | 1.00 GiB   | 7,244.31 GiB  | +64,872% |

> [!Note]
>
> - Percentage increases are calculated against Praos baseline of 11.15
>   GiB/month
> - EB sizes vary slightly with IB/s rates as they contain references to IBs
> - While Leios chain state could potentially be compressed by >70% based on
>   early experiments, this analysis uses raw storage requirements
> - Current Cardano nodes do not compress chain history, so we focus on
>   uncompressed values for practical deployment considerations

### Storage Component Analysis at Higher IB Rates

As the IB rate increases, the storage profile changes dramatically:

| IB/s | IB Storage % | EB Storage % | RB Storage % |
| ---- | ------------ | ------------ | ------------ |
| 0.05 | 92.0%        | 0.4%         | 7.6%         |
| 1    | 99.5%        | <0.1%        | 0.4%         |
| 5    | 99.9%        | <0.1%        | <0.1%        |
| 10   | >99.9%       | <0.1%        | <0.1%        |
| 20   | >99.9%       | <0.1%        | <0.1%        |
| 30   | >99.9%       | <0.1%        | <0.1%        |

This shows that as throughput increases, Input Block storage completely
dominates the requirements, comprising over 99% of storage at rates above 1
IB/s.

## Cost Analysis

### Monthly Storage Cost by Cloud Provider ($)

| Provider        | Price/GB | Free Allowance (GB) | 0.05 IB/s | 1 IB/s  | 5 IB/s  | 10 IB/s  | 20 IB/s  | 30 IB/s   |
| --------------- | -------- | ------------------- | --------- | ------- | ------- | -------- | -------- | --------- |
| Google Cloud    | $0.040   | 0                   | $0.52     | $9.70   | $48.33  | $96.62   | $193.20  | $289.77   |
| Railway         | $0.150   | 0                   | $1.97     | $36.38  | $181.24 | $362.32  | $724.48  | $1,086.65 |
| AWS             | $0.080   | 100                 | $0.00     | $11.40  | $88.66  | $185.24  | $378.39  | $571.54   |
| Microsoft Azure | $0.075   | 100                 | $0.00     | $10.69  | $83.12  | $173.66  | $357.74  | $541.82   |
| Alibaba Cloud   | $0.050   | 10                  | $0.16     | $11.63  | $59.91  | $120.27  | $241.00  | $361.72   |
| DigitalOcean    | $0.100   | 100                 | $0.00     | $14.25  | $110.83 | $231.55  | $472.99  | $714.43   |
| Oracle Cloud    | $0.0425  | 10,240              | $0.00     | $0.00   | $0.00   | $0.00    | $0.00    | $0.00     |
| Linode          | $0.100   | 1,024               | $0.00     | $0.00   | $18.43  | $139.15  | $380.59  | $622.03   |
| Hetzner         | $0.046   | 0                   | $0.60     | $11.16  | $55.58  | $111.11  | $222.17  | $333.24   |
| UpCloud         | $0.056   | 1,024               | $0.00     | $0.00   | $10.30  | $77.88   | $213.67  | $349.27   |

## Storage Cost Sources

| Provider        | Price/GB | Source                                                     | Last Updated |
| --------------- | -------- | ---------------------------------------------------------- | ------------ |
| Google Cloud    | $0.040   | https://cloud.google.com/compute/disks-image-pricing       | Feb 2025     |
| Railway         | $0.150   | https://railway.app/pricing                                | -            |
| AWS             | $0.080   | https://aws.amazon.com/ebs/pricing/                        | 2023         |
| Microsoft Azure | $0.075   | https://azure.microsoft.com/pricing/details/managed-disks/ | Dec 2024     |
| Alibaba Cloud   | $0.050   | https://www.alibabacloud.com/pricing                       | 2024         |
| DigitalOcean    | $0.100   | https://www.digitalocean.com/pricing/                      | -            |
| Oracle Cloud    | $0.0425  | https://www.oracle.com/cloud/pricing/                      | Dec 2024     |
| Linode          | $0.100   | https://www.linode.com/pricing/                            | Apr 2023     |
| Hetzner         | $0.046   | https://www.hetzner.com/cloud/pricing                      | 2024         |
| UpCloud         | $0.056   | https://upcloud.com/pricing/                               | -            |

Note: Prices may vary by region and volume. Some providers offer free tiers or
volume discounts not reflected in these base rates. The table shows the standard
storage rates for the most commonly used regions.
