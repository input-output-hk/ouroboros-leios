# Leios Node Operating Costs Analysis

## Overview

This document provides a comprehensive analysis of the costs associated with running a Leios node.

## Cost Items

| Cost Item | Unit | Description |
|-----------|------|-------------|
| Compute (vCPU) | $/vCPU/h | Cost per virtual CPU per hour |
| Compute (RAM) | $/GB/h | Cost per gigabyte of RAM per hour |
| Storage (SSD) | $/GiB/mo | Cost per gibibyte of SSD storage per month |
| Egress | $/GiB | Cost per gibibyte of data transferred out |
| Ingress | $/GiB | Cost per gibibyte of data transferred in (if applicable) |
| Static IP | $/mo | Cost per static IPv4 address per month |

> [!Note]
> Storage and data transfer use binary prefixes (GiB = 2³⁰ bytes), while RAM uses decimal prefixes (GB = 10⁹ bytes), following industry standards for cloud computing. 
































## Total Cost Analysis

This section provides a consolidated view of the three major cost components (vCPU, storage, and egress) for running a Leios node across different IB/s rates.

> [!Important]
> Storage costs accumulate over time as blockchain data grows. The monthly view below shows only the incremental storage cost for that month, while the yearly view accounts for the total accumulated storage costs.

### Monthly Total Cost by Cloud Provider ($)

| Provider    | IB/s | vCPU | Storage | Egress | Total | Notes |
|------------|------|------|---------|---------|-------|-------|
| AWS        | 1    | $124.10 | $4.72   | $172.80 | $301.62 | c6i, US East |
|            | 5    | $248.20 | $22.84  | $816.30 | $1,087.34 | |
|            | 10   | $496.40 | $45.50  | $1,625.40| $2,167.30 | |
|            | 20   | $992.80 | $90.82  | $3,243.60| $4,327.22 | |
|            | 30   | $1,985.60| $136.13 | $4,862.70| $6,984.43 | |
| GCP        | 1    | $152.35 | $2.36   | $230.40 | $385.11 | c2/n2, US Central1 |
|            | 5    | $304.78 | $11.42  | $1,088.40| $1,404.60 | |
|            | 10   | $609.48 | $22.75  | $2,167.20| $2,799.43 | |
|            | 20   | $1,219.04| $45.41  | $4,325.40| $5,589.85 | |
|            | 30   | $2,437.92| $68.07  | $6,483.60| $8,989.59 | |
| Azure      | 1    | $123.37 | $4.42   | $167.04 | $294.83 | Fsv2, East US |
|            | 5    | $246.74 | $21.42  | $788.73  | $1,056.89 | |
|            | 10   | $494.21 | $42.66  | $1,570.89| $2,107.76 | |
|            | 20   | $988.42 | $85.14  | $3,135.09| $4,208.65 | |
|            | 30   | $1,976.84| $127.63 | $4,699.29| $6,803.76 | |
| DigitalOcean| 1    | $84.00  | $5.90   | $19.20   | $109.10 | CPU-Optimized |
|            | 5    | $168.00 | $28.55  | $90.70   | $287.25 | |
|            | 10   | $336.00 | $56.88  | $180.60  | $573.48 | |
|            | 20   | $672.00 | $113.52 | $360.40  | $1,145.92| |
|            | 30   | $1,344.00| $170.17 | $540.30  | $2,054.47| |
| Hetzner    | 1    | $17.80  | $2.71   | $2.07    | $22.58 | CPX |
|            | 5    | $32.90  | $13.13  | $9.80    | $55.83 | |
|            | 10   | $65.30  | $26.16  | $19.50   | $110.96| |
|            | 20   | $130.60 | $52.22  | $38.92   | $221.74| |
|            | 30   | $261.20 | $78.28  | $58.35   | $397.83| |

### Yearly Total Cost by Cloud Provider ($)

| Provider    | IB/s | vCPU | Storage | Egress | Total | Notes |
|------------|------|------|---------|---------|-------|-------|
| AWS        | 1    | $1,489.20 | $56.64  | $2,073.60 | $3,619.44 | c6i, US East |
|            | 5    | $2,978.40 | $274.08 | $9,795.60 | $13,048.08 | |
|            | 10   | $5,956.80 | $546.00 | $19,504.80| $26,007.60 | |
|            | 20   | $11,913.60| $1,089.84| $38,923.20| $51,926.64 | |
|            | 30   | $23,827.20| $1,633.56| $58,352.40| $83,813.16 | |
| GCP        | 1    | $1,828.20 | $28.32  | $2,764.80 | $4,621.32 | c2/n2, US Central1 |
|            | 5    | $3,657.36 | $137.04 | $13,060.80| $16,855.20 | |
|            | 10   | $7,313.76 | $273.00 | $26,006.40| $33,593.16 | |
|            | 20   | $14,628.48| $544.92 | $51,904.80| $67,078.20 | |
|            | 30   | $29,255.04| $816.84 | $77,803.20| $107,875.08| |
| Azure      | 1    | $1,480.44 | $53.04  | $2,004.48 | $3,537.96 | Fsv2, East US |
|            | 5    | $2,960.88 | $257.04 | $9,464.76 | $12,682.68 | |
|            | 10   | $5,930.52 | $511.92 | $18,850.68| $25,293.12 | |
|            | 20   | $11,861.04| $1,021.68| $37,621.08| $50,503.80 | |
|            | 30   | $23,722.08| $1,531.56| $56,391.48| $81,645.12 | |
| DigitalOcean| 1    | $1,008.00 | $70.80  | $230.40   | $1,309.20 | CPU-Optimized |
|            | 5    | $2,016.00 | $342.60 | $1,088.40 | $3,447.00 | |
|            | 10   | $4,032.00 | $682.56 | $2,167.20 | $6,881.76 | |
|            | 20   | $8,064.00 | $1,362.24| $4,324.80 | $13,751.04| |
|            | 30   | $16,128.00| $2,042.04| $6,483.60 | $24,653.64| |
| Hetzner    | 1    | $213.60  | $32.52  | $24.84    | $270.96 | CPX |
|            | 5    | $394.80  | $157.56 | $117.60   | $669.96 | |
|            | 10   | $783.60  | $313.92 | $234.00   | $1,331.52| |
|            | 20   | $1,567.20 | $626.64 | $467.04   | $2,660.88| |
|            | 30   | $3,134.40 | $939.36 | $700.20   | $4,773.96| |

> [!Note]
> - Costs are based on on-demand pricing in US regions
> - vCPU costs assume compute-optimized instances
> - Storage costs include both chain state and ledger state, accumulating over time
> - Egress costs assume 20 peers with 100% header propagation and 25% body requests
> - Total costs may be reduced through:
>   - Reserved instances or longer-term commitments
>   - Volume discounts
>   - Regional pricing variations
>   - Spot/preemptible instances where available

### Cost Breakdown by Component (%)

#### Monthly
| IB/s | vCPU | Storage | Egress |
|------|------|---------|---------|
| 1    | 41%  | 2%      | 57%     |
| 5    | 23%  | 2%      | 75%     |
| 10   | 23%  | 2%      | 75%     |
| 20   | 23%  | 2%      | 75%     |
| 30   | 28%  | 2%      | 70%     |

#### Yearly
| IB/s | vCPU | Storage | Egress |
|------|------|---------|---------|
| 1    | 41%  | 2%      | 57%     |
| 5    | 23%  | 2%      | 75%     |
| 10   | 22%  | 2%      | 76%     |
| 20   | 23%  | 2%      | 75%     |
| 30   | 28%  | 2%      | 70%     |

> [!Note]
> - Percentages are averages across all providers
> - Egress remains the dominant cost component
> - Storage costs remain relatively small even when accumulated over a year
> - vCPU costs become more significant at higher IB/s rates
> - Hetzner's significantly lower costs are primarily due to their competitive egress pricing 