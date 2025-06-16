---
title: Weekly Summary – June 10, 2025
authors:
- will
tags: [progress, update, weekly, trace-processor, miniature-mainnet, topology, data-analysis, memory-optimization]
---

This week, the Leios team focused on improving simulation analysis tools and creating more practical network topologies. Key achievements include enhancing the trace processor with additional data extraction capabilities and developing a smaller, more efficient 'miniature mainnet' topology for repeated experimentation.

## Trace processor enhancements

- Enhanced the [`leios-trace-processor`](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/trace-processor/) to extract CPU, resource, and message-receipt data from simulation trace files
- Eliminated the need for using older, lower-performance scripts for analyzing simulation results
- Added comprehensive data output options:
  - Transaction lifecycle data
  - CPU utilization metrics
  - Resource consumption data
  - Message receipt tracking
- Improved analysis efficiency for large simulation datasets.

## Miniature mainnet topology

- Created a more practical 750-node topology that faithfully mimics mainnet characteristics while addressing performance limitations of the 10,000-node pseudo-mainnet
- Achieved a network diameter, stake distribution, and edge degree closely matching those of the mainnet
- Key network metrics:
  - 216 block producers and 534 relay nodes
  - 19,314 total connections with 5-hop network diameter
  - Average of 25.75 connections per node
  - Clustering coefficient of 0.332
  - Average latency of 64.8ms with maximum of 578.3ms
  - 84.85% asymmetry ratio
- Documented the methodology and results in [topology-v2.ipynb](https://github.com/input-output-hk/ouroboros-leios/blob/main/data/simulation/pseudo-mainnet/topology-v2.ipynb)
- Deployed the network configuration in [topology-v2.yaml](https://github.com/input-output-hk/ouroboros-leios/blob/main/data/simulation/pseudo-mainnet/topology-v2.yaml)
- Enabled more practical, repeatable experimentation with realistic network characteristics.
