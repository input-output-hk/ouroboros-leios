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

### Key Findings and Trade-offs

The analysis reveals important characteristics about Leios's performance at different throughput levels:

- **Low TPS Overhead**: At low TPS (10 TPS), the protocol shows significant overhead compared to Praos, with resource usage increasing by 6x for compute and 1.8x for egress. This indicates a substantial baseline cost for running Leios at low throughput.

- **Scaling Efficiency**: As TPS increases, Leios's relative overhead decreases. At 1K TPS, while absolute resource usage is higher, the protocol becomes more efficient relative to the throughput achieved.

- **Main Cost Driver**: The analysis identified that voting operations are the primary cost driver in the protocol. This finding sparked discussions about potential collaboration with Peras to reuse their voting mechanism, which could significantly reduce resource consumption and improve overall efficiency.

- **Performance Characteristics**:
  - High end: Achieves high throughput with lower-than-Praos latency
  - Low end: Poor trade-off between latency and resource overheads
  - Currently experiencing longer settlement times (quantification pending)

- **Resource Utilization**:
  - Higher overhead at low utilization, primarily driven by the cost of votes
  - Resource efficiency improves significantly at higher TPS levels
  - Requires higher utilization to justify its trade-offs

#### Recommendations
1. **Integration Opportunity**: Explore clever integration possibilities between Leios and Peras, particularly focusing on:
   - Potential reuse of Peras's voting mechanism
   - Shared resource optimization
   - Combined protocol benefits

2. **Research Needs**: 
   - Dedicated research team needed to investigate integration possibilities
   - Further quantification of settlement times and their impact
   - Detailed analysis of optimal utilization thresholds

## Next steps for cost

- calculate each cost item for different scenarios
    - one complete table with all cost items broken up
    - detailed example calculations for each cost item
- add pricing to it
- calculate possible revenue from tx fees
- possibly build tool for it
- incentives?