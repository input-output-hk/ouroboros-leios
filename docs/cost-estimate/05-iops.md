# IOPS cost estimation per node

> [!Note] 
> This analysis compares IOPS (Input/Output Operations Per Second) requirements
> between Ouroboros Praos and Linear Leios (CIP-164). IOPS is a critical metric
> that directly impacts storage performance and cloud costs.
>
> **Assumption on Votes and Certifications**: In the Leios protocol, votes are
> ephemeral and not persisted to disk. Votes are used to certify EBs, and these
> certifications are included in RBs. The certifications become part of the
> permanent blockchain record once included in an RB.

## Understanding IOPS 

IOPS (Input/Output Operations Per Second) in cloud environments are measured
based on standard-sized blocks of data. For AWS EBS volumes and similar cloud
storage services, the block size is typically 4 KiB (4,096 bytes). Each read
or write operation to a block counts as one IOPS, regardless of how much data
is actually accessed within that block.

### IOPS Conversion Formula

$$IOPS = \text{Operations} \times \left\lceil\frac{\text{DataSize}}{4{,}096}\right\rceil$$

Where:
- $\text{Operations}$ = Number of blockchain operations (reads/writes)
- $\text{DataSize}$ = Size of the data in bytes
- $\lceil\frac{\text{DataSize}}{4{,}096}\rceil$ = Ceiling to nearest whole number of 4 KiB blocks

## Ouroboros Praos

### Component Storage Operations

| Operation Type     | Logical Ops | Data Size (KiB) | 4 KiB Blocks | IOPS per Block |
| ------------------ | ----------- | --------------- | ------------ | -------------- |
| Block header write | 1           | 1               | 1            | 1              |
| Block header read  | 0.1         | 1               | 1            | 0.1            |
| Block body write   | 1           | 88              | 22           | 22             |
| Block body read    | 0.1         | 88              | 22           | 2.2            |
| State update       | 3           | 12              | 3            | 3              |
| **Total**          | **5.2**     | —               | —            | **28.3**       |

### Praos IOPS Calculation (0.05 blocks/s)

$$IOPS_{\text{praos}} = 0.05 \times 28.3 = 1.415 \text{ IOPS/s}$$

## Ouroboros Leios

In Linear Leios (CIP-164), transaction data is stored on confirmation (when an
EB is certified and applied to the ledger). UTxO-HD stores ledger state on disk,
so each confirmed transaction triggers UTxO updates.

### IOPS Components

| Component               | Description                                    | Scales With  |
| ----------------------- | ---------------------------------------------- | ------------ |
| Tx data writes          | Raw confirmed transaction bytes to disk        | TxkB/s       |
| UTxO state updates      | Insert/delete UTxO entries (LSM tree writes)   | Tx/s         |
| EB body writes          | Tx hash references in certified EB bodies      | TxkB/s       |
| RB writes/reads         | Ranking blocks with embedded certificates      | Fixed        |
| EB header writes/reads  | EB headers (small, fixed rate)                 | Fixed        |

### IOPS Formulas

1. **Transaction Data IOPS** (raw bytes, write + read):

   $$IOPS_{\text{tx-data}} = \frac{\text{TxkB/s} \times 1{,}000}{4{,}096} \times 1.1$$

   where 1.1 accounts for ~10% read-back (validation, peer serving).

2. **UTxO State Update IOPS** (dominant — per confirmed tx, LSM tree writes):

   $$IOPS_{\text{utxo}} = \frac{\text{TxkB/s} \times 1{,}000}{1{,}500} \times 3$$

   where 1,500 bytes is the average tx size and 3 IOPS/tx estimates the
   combined UTxO inserts and deletes per transaction.

   > [!Note]
   > UTxO-HD uses an LSM tree structure. In practice, writes are batched into
   > memtables and flushed periodically, so peak IOPS is lower than the raw
   > per-tx count above. The formula gives a conservative upper bound.

3. **EB Body IOPS** (tx hash references; P(cert) cancels, use $R_{\text{eb}}$):

   At 200 TxkB/s, EB body ≈ $\frac{133}{0.05} \times 32 = 85{,}333$ bytes → 21 blocks.
   $$IOPS_{\text{eb-body}} = 0.05 \times 21 \times 1.2 \approx 1.26 \text{ IOPS/s}$$

4. **RB IOPS** (fixed):

   $$IOPS_{\text{rb}} = 0.05 \times 2 \times 1.2 = 0.12 \text{ IOPS/s}$$

5. **EB Header IOPS** (fixed):

   $$IOPS_{\text{eb-hdr}} = 0.05 \times 1 \times 1.2 = 0.06 \text{ IOPS/s}$$

### IOPS at 4.5 TxkB/s (Praos-equivalent)

1. **Tx data**: $\frac{4{,}500}{4{,}096} \times 1.1 = 1.21 \text{ IOPS/s}$

2. **UTxO state**: $\frac{4{,}500}{1{,}500} \times 3 = 9.0 \text{ IOPS/s}$

3. **EB body**: $0.05 \times \lceil 1{,}920 / 4{,}096 \rceil \times 1.2 = 0.05 \times 1 \times 1.2 = 0.06 \text{ IOPS/s}$

4. **RB + EB headers**: $0.12 + 0.06 = 0.18 \text{ IOPS/s}$

5. **Total**: $1.21 + 9.0 + 0.06 + 0.18 \approx 10.45 \text{ IOPS/s}$

At 4.5 TxkB/s, Leios requires approximately 10.4 IOPS/s vs Praos' 1.4 IOPS/s,
primarily due to UTxO state updates being written to disk (UTxO-HD requirement).

### IOPS Requirements at Different Confirmed Throughputs

| TxkB/s | Tx/s | Tx Data IOPS | UTxO IOPS | EB Body IOPS | Fixed IOPS | Total IOPS/s |
| ------ | ---- | ------------ | --------- | ------------ | ---------- | ------------ |
| 4.5    | 3    | 1.21         | 9.0       | 0.06         | 0.18       | 10.45        |
| 50     | 33   | 13.4         | 100.0     | 0.36         | 0.18       | 113.9        |
| 100    | 67   | 26.9         | 200.0     | 0.66         | 0.18       | 227.7        |
| 150    | 100  | 40.3         | 300.0     | 0.96         | 0.18       | 341.4        |
| 200    | 133  | 53.7         | 400.0     | 1.26         | 0.18       | 455.1        |
| 250    | 167  | 67.1         | 500.0     | 1.62         | 0.18       | 568.9        |
| 300    | 200  | 80.6         | 600.0     | 1.92         | 0.18       | 682.7        |

> [!Note]
>
> - Tx/s assumes average transaction size of 1,500 bytes
> - UTxO state IOPS dominates due to UTxO-HD writing ledger state to disk
> - All throughput levels fit within the base IOPS included with standard
>   cloud storage volumes (typically 3,000–5,000 IOPS), so no additional
>   provisioned IOPS are required for this workload alone
> - The 3 IOPS/tx UTxO estimate is a conservative upper bound; LSM tree
>   batching in practice results in lower effective IOPS

### IOPS Component Analysis at 200 TxkB/s

| Component        | IOPS/s    | % of Total |
| ---------------- | --------- | ---------- |
| UTxO State       | 400.0     | 87.9%      |
| Tx Data Writes   | 53.7      | 11.8%      |
| EB Body          | 1.26      | 0.3%       |
| RB + EB Headers  | 0.18      | < 0.1%     |
| **Total**        | **455.1** | **100%**   |

## Monthly Cost by Cloud Provider ($)

All throughput levels remain well within the base IOPS included with standard
cloud SSD volumes. No additional provisioned IOPS are required.

| Provider     | Storage Type      | Included IOPS | 4.5 TxkB/s | 50 TxkB/s | 100 TxkB/s | 150 TxkB/s | 200 TxkB/s | 250 TxkB/s | 300 TxkB/s |
| ------------ | ----------------- | ------------- | ---------- | --------- | ---------- | ---------- | ---------- | ---------- | ---------- |
| AWS          | gp3               | 3,000         | $10        | $10       | $10        | $10        | $10        | $10        | $10        |
| GCP          | Standard PD       | 3,000         | $15        | $15       | $15        | $15        | $15        | $15        | $15        |
| Azure        | Standard SSD E    | 3,000         | $12        | $12       | $12        | $12        | $12        | $12        | $12        |
| DigitalOcean | Standard SSD      | 5,000         | $8         | $8        | $8         | $8         | $8         | $8         | $8         |
| Linode       | Standard Volume   | 5,000         | $7         | $7        | $7         | $7         | $7         | $7         | $7         |
| Hetzner      | Standard volumes  | 4,000         | $5         | $5        | $5         | $5         | $5         | $5         | $5         |

> [!Note]
>
> - Costs include the storage volume (~1 TB) and base IOPS provisioning
> - The maximum required IOPS (681.5/s at 300 TxkB/s) is well within all
>   providers' included base IOPS, so the cost is flat across throughput levels
> - For comparison, Leios at 300 TxkB/s requires ~682 IOPS/s peak vs the 3,000+
>   IOPS included as standard — a comfortable 4× headroom

### Storage Cost Sources

| Provider     | Storage Type      | Source                                                      | Last Updated |
| ------------ | ----------------- | ----------------------------------------------------------- | ------------ |
| AWS          | gp3               | https://aws.amazon.com/ebs/pricing/                         | Apr 2025     |
| GCP          | Standard PD       | https://cloud.google.com/compute/disks-image-pricing        | Apr 2025     |
| Azure        | Standard SSD      | https://azure.microsoft.com/pricing/details/managed-disks/  | Apr 2025     |
| DigitalOcean | Standard SSD      | https://www.digitalocean.com/pricing/volumes                | Apr 2025     |
| Linode       | Block Storage     | https://www.linode.com/pricing/#storage                     | Apr 2025     |
| Hetzner      | Standard volumes  | https://www.hetzner.com/cloud/pricing                       | Apr 2025     |

## Key Findings

- **Praos**: ~1.4 IOPS/s (in-memory UTxO, minimal disk writes)
- **Leios at 4.5 TxkB/s**: ~10.45 IOPS/s (7.4× Praos), driven by UTxO-HD
  disk writes that are not required in Praos
- **Leios at 300 TxkB/s**: ~683 IOPS/s, still within base cloud IOPS budgets
- IOPS is not a cost driver for Leios — standard SSD volumes are sufficient
  at all throughput levels up to the CIP-164 capacity ceiling (~288 TxkB/s)
