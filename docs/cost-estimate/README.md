# Leios Node Operating Costs Analysis

## Overview

This document provides a list of cost items that we used for our analysis of the
operational costs associated with running a Leios node. As a baseline
calculation we use Ouroboros Praos for comparisons and different block usage
percentages.

## Cost Items

| Cost Item                             | Unit      | Description                                |
| ------------------------------------- | --------- | ------------------------------------------ |
| [Compute (vCPU)](./01-compute-cpu.md) | $/vCPU/h  | Cost per virtual CPU per hour              |
| [Compute (RAM)](./02-compute-ram.md)  | $/GB/h    | Cost per gigabyte of RAM per hour          |
| [Storage (SSD)](./03-storage.md)      | $/GiB/mo  | Cost per gibibyte of SSD storage per month |
| [Egress](./04-egress.md)              | $/GiB     | Cost per gibibyte of data transferred out  |
| [IOPS](./05-iops.md)                  | $/IOPS/mo | Cost per IOPS per month                    |

Follow the links above to see detailed cost estimates per item.

## Aggregated Total Cost Table

The table below provides an aggregated summary of all cost categories across
different cloud providers based on throughput rates (IB/s).

| Provider         | Cost Item           | 0.05 IB/s   | 1 IB/s      | 5 IB/s        | 10 IB/s       | 20 IB/s       | 30 IB/s       |
| ---------------- | ------------------- | ----------- | ----------- | ------------- | ------------- | ------------- | ------------- |
| **AWS**          | Compute (vCPU)      | $62.05      | $62.05      | $124.10       | $124.10       | $248.20       | $248.20       |
|                  | Compute (RAM)       | $20.79      | $41.59      | $41.59        | $83.18        | $83.18        | $83.18        |
|                  | Storage             | $0.00       | $11.40      | $88.66        | $185.24       | $378.39       | $571.54       |
|                  | Egress              | $0.00       | $108.00     | $535.50       | $1,071.90     | $2,142.00     | $3,212.10     |
|                  | IOPS                | $10.00      | $10.00      | $15.00        | $25.00        | $50.00        | $75.00        |
|                  | **Total (AWS)**     | **$92.84**  | **$233.04** | **$804.85**   | **$1,489.42** | **$2,901.77** | **$4,190.02** |
| **GCP**          | Compute (vCPU)      | $52.34      | $52.34      | $152.35       | $152.35       | $304.78       | $304.78       |
|                  | Compute (RAM)       | $35.95      | $71.91      | $71.91        | $143.81       | $143.81       | $143.81       |
|                  | Storage             | $0.52       | $9.70       | $48.33        | $96.62        | $193.20       | $289.77       |
|                  | Egress              | $10.30      | $141.60     | $714.00       | $1,429.20     | $2,856.00     | $4,282.80     |
|                  | IOPS                | $15.00      | $15.00      | $20.00        | $35.00        | $65.00        | $95.00        |
|                  | **Total (GCP)**     | **$114.11** | **$290.55** | **$1,006.59** | **$1,856.98** | **$3,562.79** | **$5,116.16** |
| **Azure**        | Compute (vCPU)      | $61.76      | $61.76      | $123.37       | $123.37       | $246.74       | $246.74       |
|                  | Compute (RAM)       | $19.50      | $39.00      | $39.00        | $78.00        | $78.00        | $78.00        |
|                  | Storage             | $0.00       | $10.69      | $83.12        | $173.66       | $357.74       | $541.82       |
|                  | Egress              | $0.00       | $104.40     | $518.50       | $1,036.17     | $2,070.60     | $3,105.03     |
|                  | IOPS                | $12.00      | $12.00      | $18.00        | $30.00        | $60.00        | $90.00        |
|                  | **Total (Azure)**   | **$93.26**  | **$227.85** | **$781.99**   | **$1,441.20** | **$2,813.08** | **$4,061.59** |
| **DigitalOcean** | Compute (vCPU)      | $42.00      | $42.00      | $84.00        | $84.00        | $168.00       | $168.00       |
|                  | Compute (RAM)       | $16.28      | $32.56      | $32.56        | $65.12        | $65.12        | $65.12        |
|                  | Storage             | $0.00       | $14.25      | $110.83       | $231.55       | $472.99       | $714.43       |
|                  | Egress              | $0.00       | $11.80      | $59.50        | $119.10       | $238.00       | $356.90       |
|                  | IOPS                | $8.00       | $8.00       | $12.00        | $25.00        | $45.00        | $65.00        |
|                  | **Total (DO)**      | **$66.28**  | **$108.61** | **$298.89**   | **$524.77**   | **$989.11**   | **$1,369.45** |
| **Linode**       | Compute (vCPU)      | $36.00      | $36.00      | $60.00        | $60.00        | $120.00       | $120.00       |
|                  | Compute (RAM)       | $21.75      | $43.51      | $43.51        | $87.02        | $87.02        | $87.02        |
|                  | Storage             | $0.00       | $0.00       | $18.43        | $139.15       | $380.59       | $622.03       |
|                  | Egress              | $0.00       | $5.90       | $29.75        | $59.55        | $119.00       | $178.45       |
|                  | IOPS                | $7.00       | $7.00       | $10.00        | $20.00        | $40.00        | $60.00        |
|                  | **Total (Linode)**  | **$64.75**  | **$92.41**  | **$161.69**   | **$365.72**   | **$746.61**   | **$1,067.50** |
| **Hetzner**      | Compute (vCPU)      | $5.40       | $5.40       | $17.80        | $17.80        | $32.90        | $32.90        |
|                  | Compute (RAM)       | $4.98       | $9.96       | $9.96         | $19.93        | $19.93        | $19.93        |
|                  | Storage             | $0.60       | $11.16      | $55.58        | $111.11       | $222.17       | $333.24       |
|                  | Egress              | $0.00       | $0.00       | $6.43         | $12.87        | $25.70        | $38.54        |
|                  | IOPS                | $5.00       | $5.00       | $8.00         | $15.00        | $30.00        | $45.00        |
|                  | **Total (Hetzner)** | **$15.98**  | **$31.52**  | **$97.77**    | **$176.71**   | **$330.70**   | **$469.61**   |

> [!Note]
> All costs are monthly estimates in USD ($) based on the Input Blocks per
> second (IB/s) rate. Higher throughput configurations are typically dominated
> by egress costs, followed by compute and storage costs. Free tier allowances
> have been factored into calculations where applicable.

> [!Important] 
> Storage costs shown above represent only one month of
> blockchain data. As blockchain history accumulates over time, storage
> requirements and associated costs will continuously increase, particularly for
> higher IB/s rates. This compounding effect should be considered when planning
> for long-term node operation.

> [!Note] 
> Storage and data transfer use binary prefixes (GiB = 2³⁰ bytes), while
> RAM uses decimal prefixes (GB = 10⁹ bytes), following industry standards for
> cloud computing.
