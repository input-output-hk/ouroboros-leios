# Data Collection Needs

This document outlines data collection priorities for analyzing and validating the Leios protocol implementation.

## Wishlist

- **Mempool statistics**
  - Transaction rejection counts and reasons
  - Transaction entry rates
  - Transaction exit rates (included in blocks vs. expired/evicted)

- **Transaction propagation tracking**
  - Time for transactions to propagate between nodes
  - Propagation path tracing across the network
  - Latency distribution for transaction visibility
  - First-seen node identification (to detect central submission points)

- **Globally deployed node data**
  - Geographic distribution of nodes
  - Inter-node latency measurements
  - Network topology observations
  - Real-world bandwidth utilization
