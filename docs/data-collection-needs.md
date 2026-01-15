# Data Collection Needs

This document outlines data collection priorities for analyzing and validating the Leios protocol implementation.

## Wishlist

- **Mempool statistics**
  - Transaction arrival rates (to measure mempool consistency across nodes under varying load)
  - Failed/rejected transaction data (currently lost - only winning transactions are visible)

- **Fork data**
  - Fork history beyond k blocks (currently lost after stability horizon, limiting attack/chain quality analysis)

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
