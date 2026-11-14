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
in operations on blocks of data. This analysis counts one operation per 4 KiB
(4,096 bytes) read or written. That is conservative: AWS EBS counts an SSD
I/O of up to 256 KiB as one operation.

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
| UTxO state updates  | 3/tx       | $(4{,}500/1{,}132) \times 3 = 11.9$ |
| **Total**           |            | **≈ 13.2 IOPS/s**                 |

### Praos IOPS Calculation (0.05 blocks/s, UTxO-HD)

$$IOPS_{\text{praos}} = 1.265 + 11.9 \approx 13.2 \text{ IOPS/s}$$

The UTxO state updates dominate at 90%, identical to the Leios pattern — because
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
| EB body writes          | Tx references in every fetched EB body         | TxkB/s       |
| RB writes/reads         | Ranking blocks (their headers announce the EBs) with embedded certificates | Fixed |

### IOPS Formulas

1. **Transaction Data IOPS** (raw bytes, write + read):

   $$IOPS_{\text{tx-data}} = \frac{\text{TxkB/s} \times 1{,}000}{4{,}096} \times 1.1$$

   where 1.1 accounts for ~10% read-back (validation, peer serving).

2. **UTxO State Update IOPS** (dominant — per confirmed tx, LSM tree writes):

   $$IOPS_{\text{utxo}} = \frac{\text{TxkB/s} \times 1{,}000}{1{,}132} \times 3$$

   where 1,132 bytes is the average tx size (the mainnet mean over epochs
   589–661) and 3 IOPS/tx estimates the
   combined UTxO inserts and deletes per transaction. A mainnet transaction
   touches 5.4 UTxO entries (2.71 inputs and 2.70 outputs, epochs 589–661).

   > [!Note]
   > UTxO-HD uses an LSM tree structure. Writes are batched into memtables and
   > flushed periodically, so the operations per transaction stay below the 5.4
   > entries it touches. 3 per transaction is an estimate, not a measurement.

3. **EB Body IOPS** (tx references, every fetched EB):

   Every fetched EB is written, certified or not: it stays on the fast SSD until
   $k$ blocks deep. Each EB references the throughput above the 2.19 TxkB/s that RBs
   carry, divided by the certified EB rate ($0.513 \times 0.05$/s), at 37 B per
   transaction. At 200 TxkB/s, EB body ≈ $\frac{(200{,}000 - 2{,}193) / 1{,}132}{0.513 \times 0.05} \times 37 = 251{,}896$ bytes → 62 blocks.
   $$IOPS_{\text{eb-body}} = 0.05 \times 62 \times 1.2 = 3.72 \text{ IOPS/s}$$

4. **RB IOPS** (fixed; the RB header announces the EB, so there is no separate
   EB header to write):

   $$IOPS_{\text{rb}} = 0.05 \times 2 \times 1.2 = 0.12 \text{ IOPS/s}$$

### IOPS at 5 TxkB/s (Leios Baseline)

1. **Tx data**: $\frac{5{,}000}{4{,}096} \times 1.1 = 1.34 \text{ IOPS/s}$

2. **UTxO state**: $\frac{5{,}000}{1{,}132} \times 3 = 13.25 \text{ IOPS/s}$

3. **EB body**: $0.05 \times \lceil 3{,}575 / 4{,}096 \rceil \times 1.2 = 0.05 \times 1 \times 1.2 = 0.06 \text{ IOPS/s}$

4. **RB**: $0.12 \text{ IOPS/s}$

5. **Total**: $1.34 + 13.25 + 0.06 + 0.12 \approx 14.77 \text{ IOPS/s}$

At 5 TxkB/s, Leios requires only ~12% more IOPS than Praos at 4.5 TxkB/s
(14.8 vs 13.2 IOPS/s) when both use UTxO-HD. The small difference comes from
the slightly higher throughput (5 vs 4.5 TxkB/s) plus EB overhead.

### IOPS Requirements at Different Confirmed Throughputs

| TxkB/s      | Tx/s | Tx Data IOPS | UTxO IOPS | EB Body IOPS | Fixed IOPS | Total IOPS/s |
|-------------|------|--------------|-----------|--------------|------------|--------------|
| 4.5 (Praos) | 4    | 1.27         | 11.9      | —            | —          | 13.2         |
| 5           | 4    | 1.34         | 13.25     | 0.06         | 0.12       | 14.77        |
| 50          | 44   | 13.4         | 132.5     | 0.90         | 0.12       | 147.0        |
| 100         | 88   | 26.9         | 265.0     | 1.86         | 0.12       | 293.9        |
| 200         | 177  | 53.7         | 530.0     | 3.72         | 0.12       | 587.6        |
| 300         | 265  | 80.6         | 795.1     | 5.58         | 0.12       | 881.3        |

> [!Note]
>
> - Both Praos and Leios modeled with UTxO-HD; UTxO state IOPS dominates for
>   both (~90% of total) — this is a property of UTxO-HD, not of Leios
> - Tx/s assumes average transaction size of 1,132 bytes
> - The Praos "Tx Data IOPS" column captures block body writes/reads (0.05 blocks/s
>   × 22 blocks/body × 1.1 read-back); Leios uses mempool gossip writes instead
> - All throughput levels fit within the base IOPS included with standard
>   cloud storage volumes (typically 3,000–5,000 IOPS), so no additional
>   provisioned IOPS are required for this workload alone
> - The 3 IOPS/tx UTxO estimate sits below the 5.4 entries a mainnet
>   transaction touches; LSM batching keeps the operations below that. Even at
>   5.4 per transaction and the estimator's 2× headroom, a node needs about 800
>   IOPS at M2 capacity, 2,000 at 200 TxkB/s and 3,035 at 300 TxkB/s, just over
>   the 3,000 included with a volume

### IOPS Component Analysis at 200 TxkB/s

| Component       | IOPS/s    | % of Total |
|-----------------|-----------|------------|
| UTxO State      | 530.0     | 90.2%      |
| Tx Data Writes  | 53.7      | 9.1%       |
| EB Body         | 3.72      | 0.6%       |
| RB              | 0.12      | < 0.1%     |
| **Total**       | **587.6** | **100%**   |

## Monthly Cost by Cloud Provider ($)

All throughput levels remain well within the base IOPS included with standard
cloud SSD volumes. No additional provisioned IOPS are required.

| Provider     | Storage Type      | Included IOPS | 4.5 (Praos) | 5 TxkB/s | 50 TxkB/s | 100 TxkB/s | 200 TxkB/s | 300 TxkB/s |
| ------------ | ----------------- | ------------- | ----------- | --------- | --------- | ---------- | ---------- | ---------- |
| AWS          | gp3               | 3,000         | $0          | $0        | $0        | $0         | $0         | $0         |
| GCP          | pd-balanced       | 3,000         | $0          | $0        | $0        | $0         | $0         | $0         |
| Azure        | Premium SSD v2    | 3,000         | $0          | $0        | $0        | $0         | $0         | $0         |
| DigitalOcean | Plan's local disk | Not billed    | $0          | $0        | $0        | $0         | $0         | $0         |
| Akamai (Linode) | Plan's local disk | Not billed | $0          | $0        | $0        | $0         | $0         | $0         |
| Hetzner      | Plan's local NVMe | Not billed    | $0          | $0        | $0        | $0         | $0         | $0         |

> [!Note]
>
> - IOPS only; the volumes themselves are priced in [03-storage.md](./03-storage.md).
>   The hyperscalers bill IOPS only above the 3,000 included with each volume, and
>   the other three providers don't bill IOPS (prices checked on 2026-11-10)
> - The maximum required IOPS (881.3/s at 300 TxkB/s) is within all providers'
>   included base IOPS, so the cost is flat across throughput levels
> - With the estimator's 2× headroom, Leios at 300 TxkB/s needs about 1,760 IOPS
>   against the 3,000 included as standard: 1.7× to spare

### Storage Cost Sources

| Provider     | Storage Type      | Source                                                      | Last Updated |
| ------------ | ----------------- | ----------------------------------------------------------- | ------------ |
| AWS          | gp3               | https://aws.amazon.com/ebs/pricing/                         | Nov 2026     |
| GCP          | pd-balanced       | https://cloud.google.com/compute/disks-image-pricing        | Nov 2026     |
| Azure        | Premium SSD v2    | https://azure.microsoft.com/pricing/details/managed-disks/  | Nov 2026     |
| DigitalOcean | Plan's local disk | https://www.digitalocean.com/pricing/volumes                | Nov 2026     |
| Akamai (Linode) | Plan's local disk | https://www.linode.com/pricing/#storage                  | Nov 2026     |
| Hetzner      | Plan's local NVMe | https://www.hetzner.com/cloud/pricing                       | Nov 2026     |

## Key Findings

- **Praos at 4.5 TxkB/s (UTxO-HD)**: ~13.2 IOPS/s — dominated by UTxO state
  updates, same as Leios at the same throughput
- **Leios at 5 TxkB/s**: ~14.8 IOPS/s — only ~12% more than Praos at 4.5
  TxkB/s; the small difference comes from slightly higher throughput and EB overhead
- **Leios at 300 TxkB/s**: ~880 IOPS/s, still within base cloud IOPS budgets
- IOPS is not a cost driver for either protocol — standard SSD volumes are
  sufficient at all throughput levels up to the CIP-164 capacity ceiling
- UTxO state IOPS dominates at all loads for both protocols — this is a
  consequence of UTxO-HD, orthogonal to the protocol comparison
