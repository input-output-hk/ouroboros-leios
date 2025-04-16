# Compute (CPU) cost estimation per node

> [!Note] 
> This analysis assumes fully utilized block space for conservative upper bound estimation, similar to the egress analysis. We'll calculate CPU requirements at different IB/s rates.

## Base Parameters
- Stage length: 20 slots (1 second per slot)
- EBs per stage: 1.5 (average)
- RBs per stage: 1 
- Average tx size: 1,400 bytes (from mainnet data)
- IB body max size: 98,304 bytes (96 KiB)
- Transactions per IB: ~70 (98,304/1,400)

## CPU Time Calculation per Second (1 IB/s scenario)

### Input Block Processing
- IB Header validation: 1ms × 1 IB = 1ms
- IB Body validation: (50ms + 98,304×0.0005ms) × 1 IB = 99.15ms
- Transaction validation: 1.5ms × 70 txs = 105ms
Subtotal: 205.15ms

### Endorser Block Processing (1.5 EBs per stage)
- EB validation: 1ms × 1.5 EBs/20s = 0.075ms
Subtotal: 0.075ms

### Vote Processing (500 votes per stage)
- Vote validation: 0.816ms × 500 votes/20s = 20.4ms
Subtotal: 20.4ms

### Certificate Processing (1 per stage)
- Certificate validation: 130ms/20s = 6.5ms
Subtotal: 6.5ms

Total CPU time per second: ~232ms (23.2% of one CPU core)

## CPU Utilization at Different IB Rates

| IB/s | CPU Time/s | Min Cores Needed | Recommended Cores |
|------|------------|------------------|-------------------|
| 1    | 232ms      | 1                | 2                |
| 5    | 1,160ms    | 2                | 4                |
| 10   | 2,320ms    | 3                | 6                |
| 20   | 4,640ms    | 5                | 8                |
| 30   | 6,960ms    | 7                | 16               |

> [!Note]
> - "Min Cores Needed" is calculated by dividing total CPU time by 1000ms and rounding up
> - "Recommended Cores" adds redundancy for spikes and other node operations
> - This assumes even distribution of work and perfect parallelization, which is optimistic

## Monthly Cost by Cloud Provider ($)

Using standard compute-optimized instances:

| Provider    | 2 Core | 4 Core | 8 Core | 16 Core | Notes |
|------------|--------|--------|--------|---------|-------|
| AWS c6i    | $62.05 | $124.10| $248.20| $496.40 | On-demand, US East |
| GCP c2/n2  | $52.34 | $152.35| $304.78| $609.48 | On-demand, US Central1, 2-core uses n2-highcpu-2 |
| Azure Fsv2 | $61.76 | $123.37| $246.74| $494.21 | On-demand, East US |
| DO CPU-Opt | $42.00 | $84.00 | $168.00| $336.00 | Regular pricing |
| Linode     | $36.00 | $60.00 | $120.00| $240.00 | Standard pricing |
| Hetzner    | $5.40  | $17.80 | $32.90 | $65.30  | Standard pricing |

> [!Note]
> - Prices are for US regions and may vary by location
> - Assumes dedicated compute-optimized instances
> - Does not include potential savings from reserved instances or spot pricing
> - Memory requirements not considered (typically sufficient in compute-optimized instances)

## Recommendations

1. For 1-5 IB/s: 4 cores should be sufficient ($60-$152/month)
2. For 5-15 IB/s: 8 cores recommended ($120-$305/month)
3. For 15-30 IB/s: 16 cores recommended ($240-$609/month)
4. Above 30 IB/s: Consider multiple nodes or higher-end instances

Key considerations:
- These calculations assume perfect parallelization which is optimistic
- Real-world performance may require more cores due to:
  - Network stack overhead
  - OS operations
  - Uneven workload distribution
  - Memory bandwidth limitations
  - Other node operations not included in calculation

## Compute Cost Sources

| Provider | Instance Type | Source | Last Updated |
|----------|--------------|---------|--------------|
| AWS | c6i | https://aws.amazon.com/ec2/pricing/on-demand/ | Apr 2025 |
| GCP | c2/n2 | https://cloud.google.com/compute/vm-instance-pricing | Apr 2025 |
| Azure | Fsv2 | https://azure.microsoft.com/pricing/details/virtual-machines/series/ | Apr 2025 |
| DigitalOcean | CPU-Optimized | https://www.digitalocean.com/pricing/compute | Apr 2025 |
| Linode | Dedicated CPU | https://www.linode.com/pricing/ | Apr 2025 |
| Hetzner | CPX | https://www.hetzner.com/cloud/pricing | Apr 2025 |

Note: Prices shown are for US regions and may vary by location. Many providers offer significant discounts for reserved instances or longer-term commitments. The table shows standard on-demand rates for compute-optimized instances.
