# Topology Checker

A tool for analyzing and validating Ouroboros network topologies.

## Input Format

The tool accepts topology files in YAML format that conform to the
[Ouroboros topology schema](../data/simulation/topology.schema.json). The
topology describes:

- Nodes with their stake and location (cluster-based or coordinate-based)
- Producer relationships between nodes
- Network characteristics (latency, bandwidth, CPU cores)

See the [example topology](../data/simulation/topology-dense-52.yaml) for a
complete reference.

## Features

The following metrics and checks are available. Click on any metric name for
detailed information.

### Network Statistics

| Metric                                     | Description                               |
| ------------------------------------------ | ----------------------------------------- |
| [Node Counts](#network-metrics)            | Distribution of node types in the network |
| [Connection Metrics](#network-metrics)     | Network connection density                |
| [Network Diameter](#network-metrics)       | Maximum hops between any two nodes        |
| [Clustering Coefficient](#network-metrics) | Local interconnectedness measure          |
| [Latency Statistics](#network-metrics)     | Network delay measurements                |

### Stake Distribution Analysis

| Metric                                           | Description                          |
| ------------------------------------------------ | ------------------------------------ |
| [Total Stake](#stake-distribution-metrics)       | Sum of stake across all nodes        |
| [Gini Coefficient](#stake-distribution-metrics)  | Stake distribution equality measure  |
| [Top Stake Holders](#stake-distribution-metrics) | Highest stake concentration analysis |

### Connectivity Analysis

| Check                                        | Description                   |
| -------------------------------------------- | ----------------------------- |
| [Triangle Inequality](#connectivity-metrics) | Suboptimal path detection     |
| [Network Resilience](#connectivity-metrics)  | Connectivity failure analysis |

## Usage

Run the topology checker with:

```bash
cargo run -- -i <topology_file>
```

Example using the dense topology:

```bash
cargo run -- -i ../data/simulation/topology-dense-52.yaml -o report.md
```

The tool will analyze the topology and generate a report containing:

- Basic network statistics
- Stake distribution analysis
- Latency analysis
- Connectivity issues and suggestions

## Example Output

Below is an example report generated from a dense topology with 52 nodes:

```markdown
# Topology Analysis Report

Source topology: ../data/simulation/topology-dense-52.yaml

## Network Statistics

| Metric                       | Value     |
| ---------------------------- | --------- |
| Total nodes                  | 52        |
| Block producers              | 52        |
| Relay nodes                  | 0         |
| Total connections            | 312       |
| Network diameter             | 5 hops    |
| Average connections per node | 6.00      |
| Clustering coefficient       | 0.284     |
| Average latency              | 31.41 ms  |
| Maximum latency              | 138.44 ms |

## Stake Distribution

| Metric           | Value |
| ---------------- | ----- |
| Total stake      | 5200  |
| Gini coefficient | 0.000 |

### Top 5 Stake Holders

| Node   | Stake | % of Total |
| ------ | ----- | ---------- |
| node-0 | 100   | 1.92%      |
| node-1 | 100   | 1.92%      |
| node-2 | 100   | 1.92%      |
| node-3 | 100   | 1.92%      |
| node-4 | 100   | 1.92%      |

## Geographic Validation

✅ No geographic violations found
```

## Glossary

### Network Metrics

- **Network Diameter**: The maximum number of hops needed to reach any node from
  any other node. A smaller diameter (e.g., 5 hops) indicates a well-connected
  network where information can propagate quickly.

- **Clustering Coefficient** (0-1): Measures how well nodes are interconnected
  with their neighbors.
  - 0: No clustering, nodes' neighbors are not connected to each other
  - 1: Perfect clustering, all possible connections exist between neighbors
  - Example: 0.284 indicates moderate local connectivity

- **Latency**: Time delay between nodes.
  - Average latency: Mean delay across all connections
  - Maximum latency: Worst-case delay in the network
  - High latencies can impact block propagation and consensus

### Stake Distribution Metrics

- **Gini Coefficient** (0-1): Measures inequality in stake distribution.
  - 0.000: Perfect equality (all nodes have equal stake)
  - 0.500: Moderate inequality
  - 1.000: Perfect inequality (one node has all stake)
  - Lower values indicate more decentralized networks

- **Total Stake**: Sum of all stake in the network. Used as the denominator when
  calculating stake percentages.

- **Top Stake Holders**: Identifies concentration of stake.
  - Lists nodes with highest stake
  - Shows percentage of total network stake
  - Helps identify potential centralization

### Connectivity Metrics

- **Triangle Inequality Violations**: Cases where an indirect path between nodes
  has lower latency than the direct connection.
  - May indicate suboptimal network topology
  - Could suggest missing beneficial direct connections

- **Network Resilience**: Analysis of network's ability to maintain connectivity
  if nodes or connections fail.
  - Identifies critical paths
  - Suggests redundancy improvements
  - Important for network reliability

## Requirements

- Rust toolchain
- Cargo package manager
