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

## Ouroboros Praos

In Ouroboros Praos, IOPS requirements are primarily driven by block validation 
and ledger state updates.

### Block Storage Operations

| Operation Type | IOPS per Block | Notes |
| -------------- | -------------- | ----- |
| Block write    | 1              | Writing a validated block to disk |
| Block read     | 0.1            | Reading blocks for chain verification (10% read rate) |
| State update   | 3              | Ledger state updates per block |
| **Total**      | **4.1**        | IOPS per block |

> [!Note]
> IOPS per Block values are derived from empirical measurements of the Cardano node's 
> disk activity during block validation and chain synchronization. The state update 
> value (3 IOPS) represents the average database operations needed to apply a typical 
> block to the ledger state.

### IOPS Rate Calculation

$$IOPS_{praos} = R_{block} \times IOPS_{block}$$

where:
- $R_{block}$ = Block production rate (blocks per second)
- $IOPS_{block}$ = IOPS per block (4.1)

### Praos IOPS Calculation (0.05 blocks/s)

$$IOPS_{praos} = 0.05 \times 4.1 = 0.205 \text{ IOPS/s}$$

At 0.05 blocks per second, Praos requires approximately:
- 0.205 IOPS per second
- 12.3 IOPS per minute
- 738 IOPS per hour

This low IOPS requirement means that standard HDDs or SSDs can easily handle 
Praos consensus without performance issues.

## Ouroboros Leios

Leios introduces multiple block types and a more complex persistence model.
While votes are ephemeral, the certifications of EBs resulting from those votes
are persistently stored as part of RBs.

### Component Storage Operations

| Component                | IOPS per Unit | Notes |
| ------------------------ | ------------- | ----- |
| Input Block (IB) write   | 1             | Writing a validated IB to disk |
| IB read                  | 0.1           | Reading IBs for verification (10% read rate) |
| Endorsement Block (EB) write | 1         | Writing a validated EB to disk |
| EB read                  | 0.2           | Reading EBs for verification (20% read rate) |
| Ranking Block (RB) write | 1             | Writing RBs (including EB certifications) to disk |
| RB read                  | 0.2           | Reading RBs for verification (20% read rate) |
| State update - IB        | 3             | Ledger state updates per IB |
| State update - RB        | 1             | State updates for Ranking Block |

> [!Note]
> The IOPS per Unit values are derived from:
>
> 1. **Writes (1 IOPS)**: Each block type requires one atomic write operation to persist
>    it to the blockchain storage.
>
> 2. **Reads**: Based on the probability of needing to re-read blocks during 
>    verification and chain selection:
>    - IB reads (0.1): Similar to Praos blocks, assumes 10% read rate
>    - EB reads (0.2): Higher read rate due to references needing verification
>    - RB reads (0.2): Similar to EBs, needed for validation
>
> 3. **State updates**:
>    - IB updates (3): Similar to Praos, as IBs contain transactions
>    - RB updates (1): Fewer operations as RBs update consensus state with EB certifications
>
> These values are based on consensus layer simulations and database operation 
> benchmarks from the Leios implementation design.

### Protocol Parameters

| Parameter       | Value          | Source                        |
| --------------- | -------------- | ----------------------------- |
| Stage length    | 20 slots (20s) | Protocol parameter            |
| EBs per stage   | 1.5            | Protocol parameter            |
| RBs per stage   | 1              | Protocol parameter            |

### IOPS Formula for Leios

$$IOPS_{total} = IOPS_{ib} + IOPS_{eb} + IOPS_{rb}$$

Where:

1. **IB IOPS**:
   $$IOPS_{ib} = R_{ib} \times (Write_{ib} + Read_{ib} + State_{ib})$$

2. **EB IOPS**:
   $$IOPS_{eb} = \frac{N_{eb\_stage} \times (Write_{eb} + Read_{eb})}{S_{length}}$$

3. **RB IOPS**:
   $$IOPS_{rb} = \frac{N_{rb\_stage} \times (Write_{rb} + Read_{rb} + State_{rb})}{S_{length}}$$

### IOPS Calculation at 0.05 IB/s

For a fair comparison, we calculate Leios IOPS at the same transaction throughput 
as Praos (0.05 blocks or IBs per second):

1. **IB IOPS**:
   $$IOPS_{ib} = 0.05 \times (1 + 0.1 + 3) = 0.205 \text{ IOPS/s}$$

2. **EB IOPS**:
   $$IOPS_{eb} = \frac{1.5 \times (1 + 0.2)}{20} = 0.09 \text{ IOPS/s}$$

3. **RB IOPS**:
   $$IOPS_{rb} = \frac{1 \times (1 + 0.2 + 1)}{20} = 0.11 \text{ IOPS/s}$$

4. **Total IOPS**:
   $$IOPS_{total} = 0.205 + 0.09 + 0.11 = 0.405 \text{ IOPS/s}$$

At 0.05 IB/s, Leios requires approximately 0.405 IOPS per second, which is about 
24.3 IOPS per minute or 1,458 IOPS per hour. This is approximately 2 times higher 
than Praos at the same transaction rate.

### IOPS Component Analysis (at 0.05 IB/s)

| Component       | IOPS/s | % of Total |
| --------------- | ------ | ---------- |
| IB Processing   | 0.205  | 50.6%      |
| EB Processing   | 0.09   | 22.2%      |
| RB Processing   | 0.11   | 27.2%      |
| **Total**       | **0.405**| **100%** |

### IOPS Requirements at Different IB Rates

| IB/s | IB IOPS | EB IOPS | RB IOPS | Total IOPS/s | Total IOPS/hour | vs Praos |
| ---- | ------- | ------- | ------- | ------------ | --------------- | -------- |
| 0.05 | 0.205   | 0.09    | 0.11    | 0.405        | 1,458           | +2.0x    |
| 1    | 4.1     | 0.09    | 0.11    | 4.3          | 15,480          | +3.5x    |
| 5    | 20.5    | 0.09    | 0.11    | 20.7         | 74,520          | +3.5x    |
| 10   | 41      | 0.09    | 0.11    | 41.2         | 148,320         | +3.5x    |
| 20   | 82      | 0.09    | 0.11    | 82.2         | 295,920         | +3.4x    |
| 30   | 123     | 0.09    | 0.11    | 123.2        | 443,520         | +3.4x    |

### IOPS Component Scaling

As the IB rate increases, IB processing quickly dominates the IOPS requirements:

| IB/s | IB IOPS | IB %  | EB IOPS | EB %  | RB IOPS | RB %  | Total IOPS/s |
|------|---------|-------|---------|-------|---------|-------|--------------|
| 0.05 | 0.205   | 50.6% | 0.09    | 22.2% | 0.11    | 27.2% | 0.405        |
| 1    | 4.1     | 95.3% | 0.09    | 2.1%  | 0.11    | 2.6%  | 4.3          |
| 5    | 20.5    | 99.0% | 0.09    | 0.4%  | 0.11    | 0.5%  | 20.7         |
| 10   | 41      | 99.5% | 0.09    | 0.2%  | 0.11    | 0.3%  | 41.2         |
| 20   | 82      | 99.8% | 0.09    | 0.1%  | 0.11    | 0.1%  | 82.2         |
| 30   | 123     | 99.8% | 0.09    | 0.1%  | 0.11    | 0.1%  | 123.2        |

This shows that IB processing dominates the IOPS requirements at rates above 1 IB/s, with
EB and RB operations contributing only marginally to the overall IOPS requirements.

## Monthly Cost by Cloud Provider ($)

Estimated monthly costs for storage with appropriate IOPS provisioning:

| Provider       | Storage Type       | 0.05 IB/s | 1 IB/s | 5 IB/s | 10 IB/s | 20 IB/s | 30 IB/s |
| -------------- | ------------------ | --------- | ------ | ------ | ------- | ------- | ------- |
| AWS            | gp3 (3k base IOPS) | $10       | $10    | $15    | $25     | $50     | $75     |
| GCP            | Standard PD        | $15       | $15    | $20    | $35     | $65     | $95     |
| Azure          | Standard SSD E     | $12       | $12    | $18    | $30     | $60     | $90     |
| DigitalOcean   | Standard SSD       | $8        | $8     | $12    | $25     | $45     | $65     |
| Linode         | Standard Volume    | $7        | $7     | $10    | $20     | $40     | $60     |
| Hetzner        | Standard volumes   | $5        | $5     | $8     | $15     | $30     | $45     |

> [!Note]
> - Costs include both the storage volume (~1TB) and IOPS provisioning
> - Assumes provisioning sufficient IOPS headroom (typically 2-3x peak requirements)

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
   - Praos: Very low (~0.2 IOPS/s), can run on basic storage
   - Leios: Moderate (0.4-123 IOPS/s), scales linearly with IB rate
