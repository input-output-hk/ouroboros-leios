# IOPS cost estimation per node

> [!Note] 
> This analysis compares IOPS (Input/Output Operations Per Second) requirements between 
> Ouroboros Praos and Leios consensus protocols. IOPS is a critical metric that 
> directly impacts storage performance and cloud costs.
>
> **Assumption on Votes and Certifications**: In the Leios protocol, votes are ephemeral and not
> persisted to disk. Votes are used to certify EBs, and these certifications are then
> included in RBs. The certifications become part of the permanent blockchain record
> once included in an RB.

## Understanding IOPS 

IOPS (Input/Output Operations Per Second) in cloud environments are measured based on 
standard-sized blocks of data. For AWS EBS volumes and similar cloud storage services, 
the block size is typically 4 KiB (4,096 bytes). Each read or write operation to a block counts as one IOPS, 
regardless of how much data is actually accessed within that block.

### Blockchain Component Sizes

These are the typical block sizes in Praos and Leios:

| Component        | Avg Size (bytes) | Avg Size (KiB) | 4 KiB Blocks Required |
|------------------|------------------|----------------|------------------------|
| Praos Block Header | 1,024          | 1              | 1                      |
| Praos Block Body   | 90,112         | 88             | 22                     |
| IB Header        | 304              | 0.3            | 1                      |
| IB Body          | 98,304           | 96             | 24                     |
| EB               | 240 + 32/IB ref  | 0.3-0.5        | 1                      |
| Certificate      | 7,168            | 7              | 2                      |
| RB Header        | 1,024            | 1              | 1                      |
| RB Body          | 7,168            | 7              | 2                      |

### IOPS Conversion Formula

To convert from logical blockchain operations to actual IOPS:

$$IOPS = Operations \times \lceil\frac{DataSize}{4,096}\rceil$$

Where:
- $Operations$ = Number of blockchain operations (reads/writes)
- $DataSize$ = Size of the data being read/written in bytes
- $\lceil\frac{DataSize}{4,096}\rceil$ = Ceiling function to round up to the nearest whole number of 4 KiB blocks

## Ouroboros Praos

### Component Storage Operations

| Operation Type | Logical Operations | Data Size (KiB) | 4 KiB Blocks | IOPS per Block |
| -------------- | ------------------ | --------------- | ------------ | -------------- |
| Block header write | 1               | 1               | 1            | 1              |
| Block header read  | 0.1             | 1               | 1            | 0.1            |
| Block body write   | 1               | 88              | 22           | 22             |
| Block body read    | 0.1             | 88              | 22           | 2.2            |
| State update       | 3               | 12              | 3            | 3              |
| **Total**          | **5.2**         | -               | -            | **28.3**       |

> [!Note]
> State updates typically involve multiple smaller modifications spread across database pages.
> We estimate 3 blocks based on database benchmarks.

### IOPS Rate Formula

$$IOPS_{\text{praos}} = R_{\text{block}} \times IOPS_{\text{block}}$$

where:
- $R_{\text{block}}$ = Block production rate (blocks per second)
- $IOPS_{\text{block}}$ = IOPS per block (28.3)

### Praos IOPS Calculation (0.05 blocks/s)

$$IOPS_{\text{praos}} = 0.05 \times 28.3 = 1.415 \text{ IOPS/s}$$

At 0.05 blocks per second, Praos requires approximately:
- 1.415 IOPS per second
- 84.9 IOPS per minute
- 5,094 IOPS per hour
- 122,256 IOPS per day

## Ouroboros Leios

### Component Storage Operations

| Component                | Logical Operations | Data Size (KiB) | 4 KiB Blocks | IOPS per Unit |
| ------------------------ | ------------------ | --------------- | ------------ | ------------- |
| Input Block (IB) header write | 1             | 0.3             | 1            | 1             |
| IB header read           | 0.1                | 0.3             | 1            | 0.1           |
| IB body write            | 1                  | 96              | 24           | 24            |
| IB body read             | 0.1                | 96              | 24           | 2.4           |
| Endorsement Block (EB) write | 1              | 0.5             | 1            | 1             |
| EB read                  | 0.2                | 0.5             | 1            | 0.2           |
| Ranking Block (RB) header write | 1           | 1               | 1            | 1             |
| RB header read           | 0.2                | 1               | 1            | 0.2           |
| RB body (cert) write     | 1                  | 7               | 2            | 2             |
| RB body (cert) read      | 0.2                | 7               | 2            | 0.4           |
| State update - IB        | 3                  | 12              | 3            | 3             |
| State update - RB        | 1                  | 4               | 1            | 1             |

### Protocol Parameters

| Parameter       | Value          | Source                        |
| --------------- | -------------- | ----------------------------- |
| Stage length    | 20 slots (20s) | Protocol parameter            |
| EBs per stage   | 1.5            | Protocol parameter            |
| RBs per stage   | 1              | Protocol parameter            |

### IOPS Formula for Leios

$$IOPS_{\text{total}} = IOPS_{\text{ib}} + IOPS_{\text{eb}} + IOPS_{\text{rb}}$$

Where:

1. **IB IOPS**:
   $$IOPS_{\text{ib}} = R_{\text{ib}} \times (Write_{\text{ib-header}} + Read_{\text{ib-header}} + Write_{\text{ib-body}} + Read_{\text{ib-body}} + State_{\text{ib}})$$

2. **EB IOPS**:
   $$IOPS_{\text{eb}} = \frac{N_{\text{eb\_stage}} \times (Write_{\text{eb}} + Read_{\text{eb}})}{S_{\text{length}}}$$

3. **RB IOPS**:
   $$IOPS_{\text{rb}} = \frac{N_{\text{rb\_stage}} \times (Write_{\text{rb-header}} + Read_{\text{rb-header}} + Write_{\text{rb-body}} + Read_{\text{rb-body}} + State_{\text{rb}})}{S_{\text{length}}}$$

### Leios IOPS Calculation (0.05 IB/s)

For a fair comparison, we calculate Leios IOPS at the same transaction throughput as Praos (0.05 blocks or IBs per second):

1. **IB IOPS**:
   $$IOPS_{\text{ib}} = 0.05 \times (1 + 0.1 + 24 + 2.4 + 3) = 1.525 \text{ IOPS/s}$$

2. **EB IOPS**:
   $$IOPS_{\text{eb}} = \frac{1.5 \times (1 + 0.2)}{20} = 0.09 \text{ IOPS/s}$$

3. **RB IOPS**:
   $$IOPS_{\text{rb}} = \frac{1 \times (1 + 0.2 + 2 + 0.4 + 1)}{20} = 0.23 \text{ IOPS/s}$$

4. **Total IOPS**:
   $$IOPS_{\text{total}} = 1.525 + 0.09 + 0.23 = 1.845 \text{ IOPS/s}$$

At 0.05 IB/s, Leios requires approximately 1.845 IOPS per second, which is about 110.7 IOPS per minute or 6,642 IOPS per hour. This is approximately 1.3 times higher than Praos at the same transaction rate.

### IOPS Component Analysis (at 0.05 IB/s)

| Component       | IOPS/s | % of Total |
| --------------- | ------ | ---------- |
| IB Processing   | 1.525  | 82.7%      |
| EB Processing   | 0.09   | 4.9%       |
| RB Processing   | 0.23   | 12.4%      |
| **Total**       | **1.845**| **100%** |

### IOPS Requirements at Different IB Rates

| IB/s | IB IOPS | EB IOPS | RB IOPS | Total IOPS/s | Total IOPS/hour | vs Praos |
| ---- | ------- | ------- | ------- | ------------ | --------------- | -------- |
| 0.05 | 1.525   | 0.09    | 0.23    | 1.845        | 6,642           | +1.3x    |
| 1    | 30.5    | 0.09    | 0.23    | 30.82        | 110,952         | +21.8x   |
| 5    | 152.5   | 0.09    | 0.23    | 152.82       | 550,152         | +108.0x  |
| 10   | 305     | 0.09    | 0.23    | 305.32       | 1,099,152       | +215.9x  |
| 20   | 610     | 0.09    | 0.23    | 610.32       | 2,197,152       | +431.4x  |
| 30   | 915     | 0.09    | 0.23    | 915.32       | 3,295,152       | +647.1x  |

> [!Note]
> The comparison shows how IOPS requirements for Leios increase relative to Praos as transaction volume grows.

### IOPS Component Scaling

As the IB rate increases in Leios, IB processing dominates the IOPS requirements:

| IB/s | IB IOPS | IB %  | EB IOPS | EB %  | RB IOPS | RB %  | Total IOPS/s |
|------|---------|-------|---------|-------|---------|-------|--------------|
| 0.05 | 1.525   | 82.7% | 0.09    | 4.9%  | 0.23    | 12.4% | 1.845        |
| 1    | 30.5    | 99.0% | 0.09    | 0.3%  | 0.23    | 0.7%  | 30.82        |
| 5    | 152.5   | 99.8% | 0.09    | 0.1%  | 0.23    | 0.2%  | 152.82       |
| 10   | 305     | 99.9% | 0.09    | 0.0%  | 0.23    | 0.1%  | 305.32       |
| 20   | 610     | 99.9% | 0.09    | 0.0%  | 0.23    | 0.0%  | 610.32       |
| 30   | 915     | 99.9% | 0.09    | 0.0%  | 0.23    | 0.0%  | 915.32       |

## Monthly Cost by Cloud Provider ($)

Estimated monthly costs for storage with appropriate IOPS provisioning:

| Provider       | Storage Type       | Base IOPS | 0.05 IB/s | 1 IB/s | 5 IB/s | 10 IB/s | 20 IB/s | 30 IB/s |
| -------------- | ------------------ | --------- | --------- | ------ | ------ | ------- | ------- | ------- |
| AWS            | gp3               | 3,000     | $10       | $10    | $15    | $30     | $60     | $90     |
| GCP            | Standard PD        | 3,000     | $15       | $15    | $25    | $40     | $80     | $120    |
| Azure          | Standard SSD E     | 3,000     | $12       | $12    | $20    | $35     | $70     | $105    |
| DigitalOcean   | Standard SSD       | 5,000     | $8        | $8     | $12    | $30     | $55     | $80     |
| Linode         | Standard Volume    | 5,000     | $7        | $7     | $12    | $25     | $50     | $75     |
| Hetzner        | Standard volumes   | 4,000     | $5        | $5     | $10    | $20     | $40     | $60     |

> [!Note]
> - The 0.05 IB/s column applies to both Praos and Leios for equal transaction throughput comparison
> - Higher rate columns (1-30 IB/s) apply only to Leios, as Praos operates at a fixed 0.05 blocks/s
> - Costs include both the storage volume (~1TB) and IOPS provisioning
> - Assumes provisioning sufficient IOPS headroom (typically 2-3x peak requirements)
> - For Leios at rates above 5 IB/s, additional provisioned IOPS beyond base offerings are needed
> - Most cloud providers include a base level of IOPS with their storage volumes

### Storage Cost Sources

| Provider     | Storage Type   | Source                                                      | Last Updated |
| ------------ | -------------- | ----------------------------------------------------------- | ------------ |
| AWS          | gp3            | https://aws.amazon.com/ebs/pricing/                         | Apr 2025     |
| GCP          | Standard PD    | https://cloud.google.com/compute/disks-image-pricing        | Apr 2025     |
| Azure        | Standard SSD   | https://azure.microsoft.com/pricing/details/managed-disks/  | Apr 2025     |
| DigitalOcean | Standard SSD   | https://www.digitalocean.com/pricing/volumes                | Apr 2025     |
| Linode       | Block Storage  | https://www.linode.com/pricing/#storage                     | Apr 2025     |
| Hetzner      | Standard volumes | https://www.hetzner.com/cloud/pricing                     | Apr 2025     |

## Key Findings and Recommendations

**IOPS Requirements**:
   - Praos: Moderate (~1.4 IOPS/s at fixed 0.05 blocks/s), requires standard SSD storage
   - Leios: Moderate at baseline (1.8 IOPS/s at 0.05 IB/s), scaling to high (915 IOPS/s at 30 IB/s)
   - At equal transaction throughput (0.05 blocks/s), Leios requires only ~30% more IOPS than Praos
   - At higher transaction rates (>5 IB/s), Leios requires provisioned IOPS beyond base offerings

**Cost Implications**:
   - For baseline transaction throughput (0.05 IB/s), the additional cost of Leios vs. Praos is negligible
   - As Leios scales to higher transaction rates (>10 IB/s), IOPS becomes a significant cost factor
   - Standard cloud provider SSD offerings can handle Leios up to ~3 IB/s without additional provisioned IOPS

**Recommendations**:
   - For Praos or Leios at baseline throughput, provision cloud storage with at least 3,000 base IOPS
   - For Leios at high throughput (>5 IB/s), consider dedicated storage solutions with higher IOPS capabilities
   - Monitor actual IOPS usage and adjust provisioning accordingly to optimize costs
