# Topology Checker

A tool for analyzing and validating Ouroboros network topologies.

## Features

### Network Statistics

| Metric                 | Description                                                           | Example                        |
| ---------------------- | --------------------------------------------------------------------- | ------------------------------ |
| Node Counts            | Total nodes in the network, broken down by block producers and relays | Total: 52, BPs: 52, Relays: 0  |
| Connection Metrics     | Total connections and average connections per node                    | Total: 312, Avg: 6.00 per node |
| Network Diameter       | Longest shortest path between any two nodes in the network            | 5 hops                         |
| Clustering Coefficient | Measure of how well nodes are interconnected (0-1)                    | 0.284                          |
| Latency Statistics     | Average and maximum latency across all connections                    | Avg: 31.41ms, Max: 138.44ms    |

### Connectivity Analysis

| Check               | Description                                                                                    | Example Issue                                                                |
| ------------------- | ---------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------- |
| Triangle Inequality | Identifies cases where indirect paths have significantly lower latency than direct connections | "Path through Sydney (180ms) shorter than direct Frankfurt->Ashburn (300ms)" |
| Network Resilience  | Analyzes the network's ability to maintain connectivity                                        | "Critical connection between nodes X and Y, consider adding redundant paths" |

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

## Geographic Validation

✅ No geographic violations found
```

## Requirements

- Rust toolchain
- Cargo package manager
