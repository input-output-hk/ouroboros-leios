# Edinburgh Workshop Day 2 Recap

The goal is answer the question of:
How much does it cost to run a Leios node at different TPS/ throughput levels?

> [!Note]
> The following cost calculation is preliminary and is subject to possibly frequent/ drastic change.

## Cost Items

| Cost Item | Unit | Description |
|-----------|------|-------------|
| Compute (vCPU) | $/vCPU/h | Cost per virtual CPU per hour |
| Compute (RAM) | $/GB/h | Cost per gigabyte of RAM per hour |
| Storage (SSD) | $/GiB/mo | Cost per gibibyte of SSD storage per month |
| Egress | $/GiB | Cost per gibibyte of data transferred out |
| IOPS | $/IOPS | Cost per input/output operation per second for storage operations |

> [!Note]
> Storage and data transfer use binary prefixes (GiB = 2³⁰ bytes), while RAM uses decimal prefixes (GB = 10⁹ bytes), following industry standards for cloud computing. 

## Resource Usage by TPS Level

| TPS Level | IBs/Stage | Egress (GiB/month) | Storage (GiB/month) | Compute (% of Core) |
|-----------|-----------|-------------------|-------------------|-------------------|
| 10 TPS | Praos | 58 | 11 | 0.1 |
| 10 TPS | 1IB/stage | 105 (x1.8) | 12 (x1.09) | 0.6 (x6) |
| 100 TPS | 10IB/stage | 514 (x8.86) | 121 (x11) | 1.0 (x10) |
| 1K TPS | 100IB/stage | 4,602 (x79.34) | 1,250 (x113.63) | 5.3 (x53) |

> [!Note]
> The Compute column shows CPU usage as a percentage of a single core. For example, 100% means one full core is utilized, while 200% would indicate usage across two cores. This metric helps in determining the number of CPU cores needed for different TPS levels.

### Key Findings

The analysis reveals important characteristics about Leios's performance at different throughput levels:

- **Low TPS Overhead**: At low TPS (10 TPS), the protocol shows significant overhead compared to Praos, with resource usage increasing by 6x for compute and 1.8x for egress. This indicates a substantial baseline cost for running Leios at low throughput and points to more research.

- **Scaling Efficiency**: As TPS increases, Leios's relative overhead decreases. At 1K TPS, while absolute resource usage is higher, the protocol becomes more efficient relative to the throughput achieved.

- **Breakeven Point**: There exists a TPS threshold (yet to be precisely defined) where Leios's performance characteristics become more favorable compared to lower TPS levels. This suggests that Leios is particularly well-suited for high-throughput scenarios.

These findings suggest that Leios may be most economically viable in high-throughput environments, where its resource utilization becomes more efficient relative to the achieved transaction throughput.

## Next steps

- calculate each cost item for different scenarios
    - one complete table with all cost items broken up
    - detailed example calculations for each cost item
- add pricing to it
- calculate possible revenue from tx fees
- possibly build tool for it
- incentives?