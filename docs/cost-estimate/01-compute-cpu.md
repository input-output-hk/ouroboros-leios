# Compute (CPU) cost estimation per node

> [!Note] This analysis assumes fully utilized block space for conservative
> upper bound estimation.

All CPU time values in this document are derived from the simulation
configuration file (`data/simulation/config.default.yaml`), which contains
benchmark measurements for protocol operations.

## Ouroboros Praos

We start with Ouroboros Praos to establish a baseline. In Praos, CPU utilization
comes from block validation:

| Component                      | Validation Time | Source                              |
| ------------------------------ | --------------- | ----------------------------------- |
| Block header validation        | 1ms             | Same as IB header validation        |
| Block body validation constant | 50ms            | Same as IB body validation constant |
| Block body validation per byte | 0.0005ms        | Same as IB body validation per byte |

### Block Rate Calculation

| Parameter               | Value    | Formula            |
| ----------------------- | -------- | ------------------ |
| Slot length             | 1 second | Protocol parameter |
| Active slot coefficient | 0.05     | Protocol parameter |
| **Blocks per second**   | **0.05** | $$1 \times 0.05$$  |

### CPU Utilization Formula

$$C_{praos} = N_{blocks} \times (H_{validation} + B_{validation})$$

where:

- $N_{blocks}$ = Blocks per second
- $H_{validation}$ = Header validation time in ms
- $B_{validation}$ = Body validation time in ms (constant + per-byte component)

### Praos CPU Calculation (0.05 blocks/s)

$$C_{praos} = 0.05 \times (1 + (50 + 90,112 \times 0.0005))$$

$$C_{praos} = 0.05 \times (1 + 95.06)$$

$$C_{praos} = 0.05 \times 96.06 \approx 4.8\text{ ms/s}$$

Thus, Praos at 0.05 blocks/s consumes approximately 4.8ms of CPU time per
second, which is about 0.48% of a single CPU core.

## Ouroboros Leios

In Leios, CPU utilization is distributed across multiple components: Input
Blocks (IBs), Endorsement Blocks (EBs), Votes, and Certificates in Ranking
Blocks (RBs).

### Component Processing Times

| Component   | Size / Unit      | Validation Time      | Config Reference                       |
| ----------- | ---------------- | -------------------- | -------------------------------------- |
| IB Header   | 304 bytes        | 1ms                  | `ib-head-validation-cpu-time-ms`       |
| IB Body     | 98,304 bytes     | 50ms + 0.0005ms/byte | `ib-body-validation-cpu-time-ms-*`     |
| EB          | 240 bytes + refs | 1ms                  | `eb-validation-cpu-time-ms`            |
| Vote        | ~150 bytes       | 0.816ms              | `vote-validation-cpu-time-ms`          |
| Certificate | 7,168 bytes      | 140ms                | `cert-validation-cpu-time-ms-constant` |

### Base Parameters

| Parameter       | Value          | Source                        |
| --------------- | -------------- | ----------------------------- |
| Stage length    | 20 slots (20s) | `leios-stage-length-slots`    |
| EBs per stage   | 1.5            | `eb-generation-probability`   |
| RBs per stage   | 1              | Protocol parameter            |
| Votes per EB    | 600            | `vote-generation-probability` |
| Votes per stage | 900            | 600 votes/EB × 1.5 EBs/stage  |

### Base CPU Usage Formulas

1. **IB Processing CPU**:

   $$C_{ib} = N_{ib} \times (H_{ib} + B_{ib})$$
   where:
   - $N_{ib}$ = Number of IBs per second
   - $H_{ib}$ = IB header validation time (1ms)
   - $B_{ib}$ = IB body validation time (50ms + 98,304×0.0005ms = 99.15ms)

2. **EB Processing CPU**:

   $$C_{eb} = \frac{N_{eb} \times T_{eb}}{S_{length}}$$
   where:
   - $N_{eb}$ = Number of EBs per stage (1.5)
   - $T_{eb}$ = EB validation time (1ms)
   - $S_{length}$ = Stage length in seconds (20s)

3. **Vote Processing CPU**:

   $$C_{vote} = \frac{N_{votes} \times T_{vote}}{S_{length}}$$
   where:
   - $N_{votes}$ = Number of votes per stage (900)
   - $T_{vote}$ = Vote validation time (0.816ms)
   - $S_{length}$ = Stage length in seconds (20s)

4. **Certificate Processing CPU**:

   $$C_{cert} = \frac{N_{cert} \times T_{cert}}{S_{length}}$$
   where:
   - $N_{cert}$ = Number of certificates per stage (1)
   - $T_{cert}$ = Certificate validation time (140ms)
   - $S_{length}$ = Stage length in seconds (20s)

5. **Total CPU Usage**:

   $$C_{total} = C_{ib} + C_{eb} + C_{vote} + C_{cert}$$

### CPU Time Calculation at 0.05 IB/s (equivalent to Praos rate)

1. **IB Processing**:

   $$C_{ib} = 0.05 \times (1 + 99.15) = 5.01\text{ ms/s}$$

2. **EB Processing**:

   $$C_{eb} = \frac{1.5 \times 1}{20} = 0.075\text{ ms/s}$$

3. **Vote Processing**:

   $$C_{vote} = \frac{900 \times 0.816}{20} = 36.72\text{ ms/s}$$

4. **Certificate Processing**:

   $$C_{cert} = \frac{1 \times 140}{20} = 7.0\text{ ms/s}$$

5. **Total CPU Usage**:

   $$C_{total} = 5.01 + 0.075 + 36.72 + 7.0 = 48.81\text{ ms/s}$$

Thus, at 0.05 IB/s, Leios consumes approximately 48.8ms of CPU time per second,
which is about 4.9% of a single CPU core.

### CPU Utilization at Different IB Rates

| IB/s | IB Processing | EB Processing | Vote Processing | Certificate Processing | Total CPU Time/s | % of One Core | Min Cores Needed | Recommended Cores |
| ---- | ------------- | ------------- | --------------- | ---------------------- | ---------------- | ------------- | ---------------- | ----------------- |
| 0.05 | 5.01ms        | 0.075ms       | 36.72ms         | 7.0ms                  | 48.81ms          | 4.9%          | 1                | 1                 |
| 1    | 100.15ms      | 0.075ms       | 36.72ms         | 7.0ms                  | 143.95ms         | 14.4%         | 1                | 2                 |
| 5    | 500.75ms      | 0.075ms       | 36.72ms         | 7.0ms                  | 544.55ms         | 54.5%         | 1                | 2                 |
| 10   | 1,001.5ms     | 0.075ms       | 36.72ms         | 7.0ms                  | 1,045.30ms       | 104.5%        | 2                | 4                 |
| 20   | 2,003ms       | 0.075ms       | 36.72ms         | 7.0ms                  | 2,046.80ms       | 204.7%        | 3                | 6                 |
| 30   | 3,004.5ms     | 0.075ms       | 36.72ms         | 7.0ms                  | 3,048.30ms       | 304.8%        | 4                | 8                 |

> [!Note]
>
> - "Min Cores Needed" is calculated by dividing total CPU time by 1000ms and
>   rounding up
> - "Recommended Cores" adds redundancy for spikes and other node operations
> - This assumes even distribution of work and perfect parallelization, which is
>   optimistic.

### CPU Component Analysis (at 0.05 IB/s)

| Component              | CPU Time | % of Total |
| ---------------------- | -------- | ---------- |
| IB Processing          | 5.01ms   | 10.3%      |
| EB Processing          | 0.075ms  | 0.2%       |
| Vote Processing        | 36.72ms  | 75.2%      |
| Certificate Processing | 7.0ms    | 14.3%      |

This shows that at the Praos-equivalent rate of 0.05 IB/s, vote processing
dominates CPU usage (75.2%), followed by certificate processing (14.3%) and IB
processing (10.3%).

### Comparative Efficiency (Leios vs. Praos)

| IB/s | Leios CPU Time | Praos Equivalent CPU Time | Ratio (Leios:Praos) |
| ---- | -------------- | ------------------------- | ------------------- |
| 0.05 | 48.8ms         | 4.8ms                     | 10.17:1             |
| 1    | 144.0ms        | 96.1ms                    | 1.50:1              |
| 5    | 544.6ms        | 480.3ms                   | 1.13:1              |
| 10   | 1,045.3ms      | 960.6ms                   | 1.09:1              |

At 0.05 IB/s, Leios requires significantly more CPU than Praos, primarily due to
vote processing and certificate overhead. At higher throughput rates, the
relative overhead of votes and certificates diminishes, making Leios approach
the per-transaction efficiency of Praos.

## Monthly Cost by Cloud Provider ($)

Using standard compute-optimized instances:

| Provider   | 2 Core | 4 Core  | 8 Core  | Notes                  |
| ---------- | ------ | ------- | ------- | ---------------------- |
| AWS c6i    | $62.05 | $124.10 | $248.20 | On-demand, US East     |
| GCP c2/n2  | $52.34 | $152.35 | $304.78 | On-demand, US Central1 |
| Azure Fsv2 | $61.76 | $123.37 | $246.74 | On-demand, East US     |
| DO CPU-Opt | $42.00 | $84.00  | $168.00 | Regular pricing        |
| Linode     | $36.00 | $60.00  | $120.00 | Standard pricing       |
| Hetzner    | $5.40  | $17.80  | $32.90  | Standard pricing       |

> [!Note]
>
> - Prices are for US regions and may vary by location
> - Assumes dedicated compute-optimized instances
> - Does not include potential savings from reserved instances or spot pricing

## Recommendations

1. For 0.05-1 IB/s: 2 cores should be sufficient ($5-$62/month)
2. For 1-10 IB/s: 4 cores recommended ($18-$152/month)
3. For 10-30 IB/s: 8 cores recommended ($33-$305/month)
4. Above 30 IB/s: Consider multiple nodes or higher-end instances

> [!Important] 
>
> Key considerations: 
> Real-world performance may require more cores due to:
>
> - Network stack overhead
> - OS operations
> - Uneven workload distribution
> - Memory bandwidth limitations
> - Other node operations not included in calculation

## Compute Cost Sources

| Provider     | Instance Type | Source                                                               | Last Updated |
| ------------ | ------------- | -------------------------------------------------------------------- | ------------ |
| AWS          | c6i           | https://aws.amazon.com/ec2/pricing/on-demand/                        | Apr 2025     |
| GCP          | c2/n2         | https://cloud.google.com/compute/vm-instance-pricing                 | Apr 2025     |
| Azure        | Fsv2          | https://azure.microsoft.com/pricing/details/virtual-machines/series/ | Apr 2025     |
| DigitalOcean | CPU-Optimized | https://www.digitalocean.com/pricing/compute                         | Apr 2025     |
| Linode       | Dedicated CPU | https://www.linode.com/pricing/                                      | Apr 2025     |
| Hetzner      | CPX           | https://www.hetzner.com/cloud/pricing                                | Apr 2025     |

Note: Prices shown are for US regions and may vary by location. Many providers
offer significant discounts for reserved instances or longer-term commitments.
The table shows standard on-demand rates for compute-optimized instances.
