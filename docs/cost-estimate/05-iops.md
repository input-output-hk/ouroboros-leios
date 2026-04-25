# IOPS cost estimation per node

> [!Note] 
> This analysis compares IOPS (Input/Output Operations Per Second) requirements
> between Ouroboros Praos and Linear Leios (CIP-164). IOPS is a critical metric
> that directly impacts storage performance and cloud costs.
>
> **UTxO-HD assumption**: Both Praos and Leios are modeled with UTxO-HD
> deployed (ledger state on disk). UTxO-HD is orthogonal to the protocol
> comparison; see `02-compute-ram.md`. Without UTxO-HD, UTxO state IOPS
> (the dominant component) would be near zero for both protocols.
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

## Ouroboros Praos (with UTxO-HD)

### Component Storage Operations

With UTxO-HD, the periodic in-memory "state update" checkpoint is replaced by
per-transaction UTxO inserts/deletes written to the LSM-tree on disk.

| Operation Type      | Rate       | IOPS/s                            |
| ------------------- | ---------- | --------------------------------- |
| Block header write  | 0.05/s     | $0.05 \times 1 = 0.05$            |
| Block header read   | 0.05×0.1/s | $0.05 \times 0.1 = 0.005$         |
| Block body write    | 0.05/s     | $0.05 \times 22 = 1.10$           |
| Block body read     | 0.05×0.1/s | $0.05 \times 2.2 = 0.11$          |
| UTxO state updates  | 3/tx       | $(4{,}500/1{,}500) \times 3 = 9.0$ |
| **Total**           |            | **≈ 10.3 IOPS/s**                 |

### Praos IOPS Calculation (0.05 blocks/s, UTxO-HD)

$$IOPS_{\text{praos}} = 1.265 + 9.0 \approx 10.3 \text{ IOPS/s}$$

The UTxO state updates dominate at 87%, identical to the Leios pattern — because
UTxO writes scale with confirmed transaction rate regardless of protocol.

## Ouroboros Leios

In Linear Leios (CIP-164), transaction data is stored on confirmation (when an
EB is certified and applied to the ledger). With UTxO-HD (same as Praos above),
each confirmed transaction triggers UTxO state updates on disk.

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

5. **EB Header IOPS** (certified EBs only):

   Uncertified EB headers are not written to disk; only certified ones persist.
   $$IOPS_{\text{eb-hdr}} = R_{\text{cert}} \times 1 \times 1.2 = 0.024 \times 1 \times 1.2 = 0.029 \text{ IOPS/s}$$

### IOPS at 5 TxkB/s (Leios Baseline)

1. **Tx data**: $\frac{5{,}000}{4{,}096} \times 1.1 = 1.34 \text{ IOPS/s}$

2. **UTxO state**: $\frac{5{,}000}{1{,}500} \times 3 = 10.0 \text{ IOPS/s}$

3. **EB body**: $0.05 \times \lceil 2{,}133 / 4{,}096 \rceil \times 1.2 = 0.05 \times 1 \times 1.2 = 0.06 \text{ IOPS/s}$

4. **RB + EB headers**: $0.12 + 0.029 = 0.149 \text{ IOPS/s}$

5. **Total**: $1.34 + 10.0 + 0.06 + 0.149 \approx 11.55 \text{ IOPS/s}$

At 5 TxkB/s, Leios requires only ~12% more IOPS than Praos at 4.5 TxkB/s
(11.6 vs 10.3 IOPS/s) when both use UTxO-HD. The small difference comes from
the slightly higher throughput (5 vs 4.5 TxkB/s) plus EB overhead.

### IOPS Requirements at Different Confirmed Throughputs

| TxkB/s      | Tx/s | Tx Data IOPS | UTxO IOPS | EB Body IOPS | Fixed IOPS | Total IOPS/s |
|-------------|------|--------------|-----------|--------------|------------|--------------|
| 4.5 (Praos) | 3    | 1.27         | 9.0       | —            | —          | 10.3         |
| 5           | 3    | 1.34         | 10.0      | 0.06         | 0.15       | 11.55        |
| 50          | 33   | 13.4         | 100.0     | 0.36         | 0.15       | 113.9        |
| 100         | 67   | 26.9         | 200.0     | 0.66         | 0.15       | 227.7        |
| 200         | 133  | 53.7         | 400.0     | 1.26         | 0.15       | 455.1        |
| 300         | 200  | 80.6         | 600.0     | 1.92         | 0.15       | 682.7        |

> [!Note]
>
> - Both Praos and Leios modeled with UTxO-HD; UTxO state IOPS dominates for
>   both (~87–88% of total) — this is a property of UTxO-HD, not of Leios
> - Tx/s assumes average transaction size of 1,500 bytes
> - The Praos "Tx Data IOPS" column captures block body writes/reads (0.05 blocks/s
>   × 22 blocks/body × 1.1 read-back); Leios uses mempool gossip writes instead
> - All throughput levels fit within the base IOPS included with standard
>   cloud storage volumes (typically 3,000–5,000 IOPS), so no additional
>   provisioned IOPS are required for this workload alone
> - The 3 IOPS/tx UTxO estimate is a conservative upper bound; LSM tree
>   batching in practice results in lower effective IOPS

### IOPS Component Analysis at 200 TxkB/s

| Component       | IOPS/s    | % of Total |
|-----------------|-----------|------------|
| UTxO State      | 400.0     | 87.9%      |
| Tx Data Writes  | 53.7      | 11.8%      |
| EB Body         | 1.26      | 0.3%       |
| RB + EB Headers | 0.15      | < 0.1%     |
| **Total**       | **455.1** | **100%**   |

## Monthly Cost by Cloud Provider ($)

All throughput levels remain well within the base IOPS included with standard
cloud SSD volumes. No additional provisioned IOPS are required.

| Provider     | Storage Type      | Included IOPS | 4.5 (Praos) | 5 TxkB/s | 50 TxkB/s | 100 TxkB/s | 200 TxkB/s | 300 TxkB/s |
| ------------ | ----------------- | ------------- | ----------- | --------- | --------- | ---------- | ---------- | ---------- |
| AWS          | gp3               | 3,000         | $10         | $10       | $10       | $10        | $10        | $10        |
| GCP          | Standard PD       | 3,000         | $15         | $15       | $15       | $15        | $15        | $15        |
| Azure        | Standard SSD E    | 3,000         | $12         | $12       | $12       | $12        | $12        | $12        |
| DigitalOcean | Standard SSD      | 5,000         | $8          | $8        | $8        | $8         | $8         | $8         |
| Linode       | Standard Volume   | 5,000         | $7          | $7        | $7        | $7         | $7         | $7         |
| Hetzner      | Standard volumes  | 4,000         | $5          | $5        | $5        | $5         | $5         | $5         |

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

- **Praos at 4.5 TxkB/s (UTxO-HD)**: ~10.3 IOPS/s — dominated by UTxO state
  updates, same as Leios at the same throughput
- **Leios at 5 TxkB/s**: ~11.6 IOPS/s — only ~12% more than Praos at 4.5
  TxkB/s; the small difference comes from slightly higher throughput and EB overhead
- **Leios at 300 TxkB/s**: ~683 IOPS/s, still within base cloud IOPS budgets
- IOPS is not a cost driver for either protocol — standard SSD volumes are
  sufficient at all throughput levels up to the CIP-164 capacity ceiling
- UTxO state IOPS dominates at all loads for both protocols — this is a
  consequence of UTxO-HD, orthogonal to the protocol comparison
