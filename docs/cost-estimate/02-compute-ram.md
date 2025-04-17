# Compute (RAM) cost estimation per node

> [!Note] 
> This analysis compares memory requirements between Ouroboros Praos and Leios
> consensus protocols. For detailed technical background on the UTxO DB design,
> see the [technical report](https://github.com/IntersectMBO/ouroboros-consensus/tree/main/docs/tech-reports/utxo-db).

## Ouroboros Praos

In Ouroboros Praos, the entire ledger state is stored in memory, which creates a
direct correlation between ledger size and RAM requirements.

### Memory Component Sizes

| Component            | Typical Size | Scaling Factor             |
| -------------------- | ------------ | -------------------------- |
| Base Node Process    | 500 MB       | Fixed                      |
| UTxO Set             | 4-8 GB       | Linear with network usage  |
| Stake Data           | 200-500 MB   | Linear with stake pools    |
| Mempool              | 64-128 MB    | Configurable               |
| Block Processing     | 100-200 MB   | Scales with block size     |
| Other Runtime Data   | 200-500 MB   | Varies                     |

### Memory Usage Formula

$$M_{praos} = M_{base} + M_{utxo} + M_{stake} + M_{mempool} + M_{processing} + M_{runtime}$$

where:
- $M_{base}$ = Base process memory (500 MB)
- $M_{utxo}$ = UTxO set size (varies with network activity)
- $M_{stake}$ = Stake distribution data
- $M_{mempool}$ = Mempool size (configurable)
- $M_{processing}$ = Block processing memory
- $M_{runtime}$ = Other runtime data

### Current State & Projection

Based on empirical measurements and ledger growth models:

| UTxO Entries (Millions) | Stake Keys (Millions) | Estimated RAM |
| ----------------------- | --------------------- | ------------- |
| 2                       | 0.4                   | 13 GB         |
| 10                      | 2                     | 30-40 GB      |
| 50                      | 10                    | 150-200 GB    |
| 100                     | 20                    | 300-400 GB    |

At high transaction rates, the UTxO set growth makes this approach prohibitively
expensive for decentralized participation.

## Ouroboros Leios

Leios solves the memory scaling problem by moving most of the UTxO set to disk,
fundamentally changing the relationship between ledger size and RAM requirements.

### Memory Usage Strategy

According to the [UTxO DB technical report](https://github.com/IntersectMBO/ouroboros-consensus/tree/main/docs/tech-reports/utxo-db), 
Leios uses key-value store technology with on-disk persistent storage for the majority of the ledger state.
The implementation favors write-optimized structures (e.g., LSM trees) and keeps only critical components in memory.

### Memory Component Formula

$$M_{leios} = M_{base} + M_{cache} + M_{indexes} + M_{buffers} + M_{stake} + M_{mempool} + M_{consensus}$$

where:
- $M_{base}$ = Base process memory (500 MB)
- $M_{cache}$ = Hot UTxO cache (200-500 MB)
- $M_{indexes}$ = In-memory indexes and filters (100-300 MB)
- $M_{buffers}$ = Write buffers (100-500 MB)
- $M_{stake}$ = Stake distribution data
- $M_{mempool}$ = Mempool size
- $M_{consensus}$ = Consensus mechanism overhead (votes, certificates, etc.)

### Memory Component Sizes

| Component              | Size Range   | Scaling Behavior                  |
| ---------------------- | ------------ | --------------------------------- |
| Base Node Process      | 500 MB       | Fixed                             |
| Hot UTxO Cache         | 200-500 MB   | Configurable, minimal with IB/s   |
| Indexes & Filters      | 100-300 MB   | Logarithmic with ledger size      |
| Write Buffers          | 100-500 MB   | Linear with transaction rate      |
| Stake Data             | 200-500 MB   | Linear with stake pool count      |
| Vote Processing        | 50-100 MB    | Minimal with IB/s                 |
| Certificate Processing | 20-40 MB     | Minimal with IB/s                 |
| Consensus Overhead     | 100-300 MB   | Varies with network parameters    |

### Calculation by Input Block Rate

| IB/s | Base (MB) | Cache (MB) | Indexes (MB) | Buffers (MB) | Stake (MB) | Consensus (MB) | Total RAM (GB) | % vs Praos |
| ---- | --------- | ---------- | ------------ | ------------ | ---------- | -------------- | -------------- | ---------- |
| 0.05 | 500       | 200        | 100          | 100          | 300        | 300            | 1.5            | 12%        |
| 1    | 500       | 300        | 150          | 200          | 300        | 350            | 1.8            | 5%         |
| 5    | 500       | 400        | 200          | 300          | 300        | 400            | 2.1            | 1.4%       |
| 10   | 500       | 450        | 250          | 350          | 300        | 450            | 2.3            | 0.8%       |
| 20   | 500       | 500        | 300          | 400          | 300        | 500            | 2.5            | 0.6%       |
| 30   | 500       | 500        | 300          | 500          | 300        | 550            | 2.7            | 0.7%       |

Percentage comparison assumes corresponding Praos values of 13GB, 40GB, 150GB, 300GB, 450GB, and 400GB.

### Disk Requirements and I/O Performance

While RAM usage is significantly reduced, I/O performance becomes the limiting factor:

| IB/s | UTxO Size on Disk | Other Ledger Data | Min IOPS Required |
| ---- | ----------------- | ----------------- | ----------------- |
| 0.05 | 4-8 GB            | 2-4 GB            | 50-200            |
| 1    | 8-15 GB           | 3-6 GB            | 1,000-2,000       |
| 5    | 15-30 GB          | 5-10 GB           | 5,000-10,000      |
| 10   | 30-60 GB          | 8-16 GB           | 10,000-20,000     |
| 20   | 60-120 GB         | 15-30 GB          | 20,000-40,000     |
| 30   | 90-180 GB         | 20-40 GB          | 30,000-60,000     |

> [!Important]
> High-performance storage is essential for Leios at higher transaction rates. NVMe SSDs 
> with sufficient IOPS capacity are required for rates above 5 IB/s.

## Monthly Cost by Cloud Provider ($)

Using the latest pricing data (April 2025) for various cloud providers, we can calculate the monthly costs for running nodes with different RAM configurations:

| Provider      | 4 GB RAM   | 8 GB RAM   | 16 GB RAM  | Notes                         |
| ------------- | ---------- | ---------- | ---------- | ----------------------------- |
| AWS           | $20.79     | $41.59     | $83.18     | t3.medium/large/xlarge       |
| Azure         | $19.50     | $39.00     | $78.00     | Standard_B2s and equivalents  |
| Google Cloud  | $35.95     | $71.91     | $143.81    | n2-standard series           |
| Railway       | $40.47     | $80.94     | $161.88    | Usage-based pricing           |
| Alibaba Cloud | $43.07     | $86.14     | $172.28    | ecs.n4.large and equivalents  |
| DigitalOcean  | $16.28     | $32.56     | $65.12     | Basic Droplets                |
| Oracle Cloud  | $8.25      | $16.50     | $33.00     | VM.Standard.E3.x series       |
| Linode        | $21.75     | $43.51     | $87.02     | Dedicated CPU instances       |
| Hetzner       | $4.98      | $9.96      | $19.93     | CX series                     |
| UpCloud       | $16.28     | $32.56     | $65.12     | General Purpose instances     |

> [!Note]
> Monthly costs calculated using: hourly rate × 730 hours/month (24 hours × 30.4 days)

### Cost Comparison: Praos vs Leios

| Throughput       | Praos RAM Needed | Praos Cost Range  | Leios RAM Needed | Leios Cost Range  | Monthly Savings |
| ---------------- | ---------------- | ----------------- | ---------------- | ----------------- | --------------- |
| 0.05 blocks/s    | 4-8 GB           | $5-86             | 2-3 GB           | $2.5-30           | $2.5-56 (50-65%)|
| 1-5 IB/s         | 8-16 GB          | $10-172           | 2-4 GB           | $2.5-43           | $7.5-129 (75%+) |
| 10-30 IB/s       | 16-32+ GB        | $20-344+          | 3-7 GB           | $3.7-80           | $16.3-264+ (80%+)|

> [!Note]
> Cost ranges use average values across all providers, from most economical (Hetzner) to premium options (Google Cloud, Railway). For Leios, standard or compute-optimized instances may be more appropriate given the lower memory requirements, but will need to include high-performance SSDs.

## RAM Cost Sources

| Provider      | Instance Type      | Source                                                 | Last Updated |
| ------------- | ------------------ | ------------------------------------------------------ | ------------ |
| AWS           | t3 series          | https://aws.amazon.com/ec2/pricing/                    | Apr 2025     |
| Azure         | Standard_B2s       | https://azure.microsoft.com/pricing/details/virtual-machines/ | Apr 2025 |
| Google Cloud  | n2-standard        | https://cloud.google.com/compute/vm-instance-pricing   | Apr 2025     |
| Railway       | Usage-based        | https://railway.app/pricing                            | Apr 2025     |
| Alibaba Cloud | ecs.n4.large       | Third-party benchmarks (VPSBenchmarks)                 | Apr 2025     |
| DigitalOcean  | Basic Droplets     | https://www.digitalocean.com/pricing/droplets          | Apr 2025     |
| Oracle Cloud  | VM.Standard.E3.x   | https://www.oracle.com/cloud/pricing/                  | Apr 2025     |
| Linode        | Dedicated CPU      | https://www.linode.com/pricing/                        | Apr 2025     |
| Hetzner       | CX series          | https://www.hetzner.com/cloud/pricing                  | Apr 2025     |
| UpCloud       | General Purpose    | https://upcloud.com/pricing/                           | Apr 2025     |

Note: Prices shown are based on standard/on-demand rates. Many providers offer significant discounts for reserved instances or longer-term commitments. All prices are subject to change and may vary by region.

## Key Findings and Recommendations

1. **RAM Requirements**:
   - Praos: 4-8 GB RAM (minimum), 8-16 GB (recommended), 16-32+ GB (high throughput)
   - Leios: 1.5-2 GB RAM (minimum), 2-4 GB (typical), 2.5-3 GB (high throughput)

2. **Storage Requirements for Leios**:
   - SSD storage is mandatory for all deployment scenarios
   - NVMe SSDs are essential for IB rates above 5 IB/s
   - IOPS capacity is the critical metric, not just disk size
   - Provision 2-3x the calculated disk space for future growth

3. **Monthly Cost Savings**: 
   - 50-65% savings at baseline throughput (0.05 blocks/s)
   - 75%+ savings at medium throughput (1-5 IB/s)
   - 80%+ savings at high throughput (10-30 IB/s)

4. **Performance Considerations**:
   - Leios shifts bottleneck from RAM to I/O performance
   - High transaction rates require investment in storage performance
   - For large ledger states (100M+ UTxOs), Leios is the only viable approach
