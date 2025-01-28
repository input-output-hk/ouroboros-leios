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
| [Connection Symmetry](#network-metrics)    | Analysis of bidirectional connections     |
| [Stake-Weighted Metrics](#network-metrics) | Impact of topology on high-stake nodes    |
| [Hop Analysis](#hop-analysis)              | Per-hop reachability and latency analysis |

### Stake Distribution Analysis

| Metric                                                 | Description                           |
| ------------------------------------------------------ | ------------------------------------- |
| [Total Stake](#stake-distribution-metrics)             | Sum of stake across all nodes         |
| [Gini Coefficient](#stake-distribution-metrics)        | Stake distribution equality measure   |
| [Top Stake Holders](#stake-distribution-metrics)       | Highest stake concentration analysis  |
| [Geographic Distribution](#stake-distribution-metrics) | Regional stake concentration analysis |

### Connectivity Analysis

| Check                                        | Description                   |
| -------------------------------------------- | ----------------------------- |
| [Triangle Inequality](#connectivity-metrics) | Suboptimal path detection     |
| [Network Resilience](#connectivity-metrics)  | Connectivity failure analysis |

## Usage

Run the topology checker with:

```bash
cargo run -- -i <topology_file> [-o <output_file>] [-n <start_node>]
```

Options:

- `-i, --input`: Input topology file (required)
- `-o, --output`: Output report file (optional, prints to stdout if not
  specified)
- `-n, --start-node`: Starting node for hop analysis (optional)

Examples:

Basic analysis:

```bash
cargo run -- -i ../data/simulation/topology-dense-52.yaml
```

Save report to file:

```bash
cargo run -- -i ../data/simulation/topology-dense-52.yaml -o report.md
```

Analyze hops from specific node:

```bash
cargo run -- -i ../data/simulation/topology-dense-52.yaml -n node-0
```

The tool will analyze the topology and generate a report containing:

- Basic network statistics
- Stake distribution analysis
- Latency analysis
- Connectivity issues and suggestions
- Hop-by-hop analysis (if start node specified)

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
| Stake-weighted latency       | 35.62 ms  |
| Bidirectional connections    | 156       |
| Asymmetric connections       | 68        |
| Asymmetry ratio              | 21.79%    |

## Network Reliability

The following nodes, if removed, would isolate significant stake:

| Node    | Isolated Stake | % of Total Stake |
| ------- | -------------- | ---------------- |
| node-12 | 800            | 15.38%           |
| node-45 | 600            | 11.54%           |
| node-31 | 400            | 7.69%            |

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

### Geographic Stake Distribution

| Region         | Nodes | Total Stake | % of Network |
| -------------- | ----- | ----------- | ------------ |
| ap-southeast-2 | 17    | 1700        | 32.69%       |
| eu-central-1   | 18    | 1800        | 34.62%       |
| us-east-1      | 17    | 1700        | 32.69%       |

## Geographic Validation

✅ No geographic violations found
```

## Glossary

### Network Metrics

- **Network Diameter**: The maximum number of hops needed to reach any node from
  any other node. A smaller diameter (e.g., 5 hops) indicates a well-connected
  network where information can propagate quickly.

- **Connection Symmetry**: Analysis of bidirectional connectivity between nodes.
  - Bidirectional Connections: Number of node pairs with connections in both
    directions
  - Asymmetric Connections: Number of one-way connections between nodes
  - Asymmetry Ratio: Percentage of total connections that are asymmetric
  - Important for understanding communication patterns and potential bottlenecks

- **Clustering Coefficient** (0-1): Measures how well nodes are interconnected
  with their neighbors.
  - 0: No clustering, nodes' neighbors are not connected to each other
  - 1: Perfect clustering, all possible connections exist between neighbors
  - Example: 0.284 indicates moderate local connectivity

- **Latency**: Time delay between nodes.
  - Average latency: Mean delay across all connections
  - Maximum latency: Worst-case delay in the network
  - High latencies can impact block propagation and consensus

- **Stake-Weighted Metrics**: Analysis of network properties weighted by stake.
  - Stake-Weighted Latency: Average latency weighted by stake importance
    - For each connection, weight = (stake of connecting node) × (stake of
      producer node)
    - Higher weights make latencies between high-stake nodes more significant
    - Lower values indicate better connectivity between important nodes
    - Higher values suggest high-stake nodes might have suboptimal connections
  - Network Reliability: Analysis of stake isolation risk
    - Lists nodes whose failure would disconnect portions of stake from the
      network
    - Shows percentage of total stake that would be isolated
    - Helps identify critical nodes for network resilience

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

- **Geographic Distribution**: Analysis of stake distribution across
  regions/clusters.
  - Shows stake concentration by region
  - Indicates regional node density
  - Helps identify geographic centralization risks
  - Important for network resilience against regional outages

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

### Hop Analysis

The hop analysis provides detailed information about network reachability and
latency from a specified starting node:

- **Hop Number**: Distance in hops from the start node
- **Latency Distribution**: latency CDF to reach nodes at this hop level

Example hop analysis output:

```markdown
### Raw Latencies per Hop

Hop 0: CDF[(0.000, 1.000)]

Hop 1: CDF[(0.170, 0.167),(0.173, 0.333),(0.174, 0.500),(0.183, 0.667),(45.240, 0.833),(138.047, 1.000)]

Hop 2: CDF[(0.150, 0.143),(0.154, 0.214),(0.169, 0.286),(0.173, 0.357),(0.180, 0.500),(0.185, 0.571),(0.190, 0.643),(0.201, 0.714),(0.219, 0.786),(0.222, 0.857),(0.235, 0.929),(134.511, 1.000)]

Hop 3: CDF[(0.144, 0.056),(0.149, 0.111),(0.150, 0.167),(0.151, 0.222),(0.156, 0.278),(0.172, 0.333),(0.174, 0.389),(0.181, 0.500),(0.184, 0.556),(0.185, 0.611),(0.190, 0.667),(0.198, 0.722),(0.213, 0.778),(0.220, 0.833),(0.228, 0.889),(0.231, 0.944),(134.570, 1.000)]

Hop 4: CDF[(0.147, 0.091),(0.149, 0.182),(0.152, 0.273),(0.155, 0.364),(0.180, 0.455),(0.202, 0.545),(0.207, 0.636),(0.209, 0.727),(0.225, 0.818),(0.229, 0.909),(136.010, 1.000)]

Hop 5: CDF[(0.144, 0.500),(0.227, 1.000)]
```

This analysis is useful for understanding:

- Network coverage from any starting point
- Latency distribution at different hop distances
- How quickly information can propagate through the network
- Potential bottlenecks or areas for optimization

When not providing a starting node, the hop analysis will be performed from all nodes and the results are shown in an aggregated form:

```
## All Paths Analysis

| Hop |  Min  |  Avg  |  Max  |
|-----|-------|-------|-------|
|   0 |  1.00 |  1.00 |  1.00 |
|   1 |  4.00 |  6.00 |  7.00 |
|   2 | 14.00 | 15.46 | 18.00 |
|   3 | 17.00 | 17.58 | 19.00 |
|   4 |  9.00 | 10.81 | 13.00 |
|   5 |  0.00 |  1.15 |  2.00 |

hop0_min := CDF[(0, 1)]
hop0_avg := CDF[(0, 1)]
hop0_max := CDF[(0, 1)]
hop1_min := CDF[(0.21418, 0.14286), ... ]
hop1_avg := CDF[(0.14073, 0.00321), ... ]
hop1_max := CDF[(0.14073, 0.16667), ... ]
hop2_min := CDF[(0.18035, 0.05882), ... ]
hop2_avg := CDF[(0.14073, 0.00377), ... ]
hop2_max := CDF[(0.14073, 0.06667), ... ]
hop3_min := CDF[(0.15032, 0.05556), ... ]
hop3_avg := CDF[(0.14073, 0.00333), ... ]
hop3_max := CDF[(0.14073, 0.05882), ... ]
hop4_min := CDF[(0.17683, 0.08333), ... ]
hop4_avg := CDF[(0.14073, 0.0035), ... ]
hop4_max := CDF[(0.14073, 0.09091), ... ]
hop5_min := CDF[(100.09514, 0.5), (136.51146, 1)]
hop5_avg := CDF[(0.14361, 0.03659), ... ]
hop5_max := CDF[(0.14361, 1)]
```

The first table shows the min/avg/max of the hops reached per distance, followed by the latency distributions' min/avg/max aggregations at each hop distance (given in `ms`).
Note that here `min` means minimal progress, i.e. the worst case, while `max` means maximal progress, i.e. the best case.

### Thoughts on relating this to a ΔQSD model

The naive way to use the above information is to build up a ΔQ expression as a series of choices after the initial hop:

- either we’re finished (weighted 1 for the origin node), or we continue sending to hop1 peers (weighted N−1)
- either we’re finished (weighted 6 for hop 1 average), or we continue sending to hop2 peers (weighted N−7)
- and so on, until after hop 4 we just send to hop5 peers and be done

When sending to some hop’s peers we might use the `*_min` or `*_avg` distributions to model what happens at this hop.
However, the way ΔQ expressions are evaluated does not fit what actually happens in the network: when sequencing two ΔQ expressions, partial completion of the first one triggers an equal part of the second one to commence.
This is not how the gossip graph behaves, though, because having reached a near peer (i.e. very quickly) does NOT unlock following up on sending from the next hop in general, it only unlocks sending from that near peer.
Reaching faraway nodes requires long latency communication and relaying from that faraway peer to others can only happen after that delay has elapsed, it cannot probabilistically occur any sooner.

This means that we cannot just build up an expression like

    hop0_avg ->- (TOP 1<>99 hop1_avg ->- (TOP 6<>93 hop2_avg ->- ...))

This is obvious from the example output shown above, which would result in a positive probability of completion from hop 5 at times as early as 101ms.

Instead of this naive model, we need to consider the gossip network as a naturally tiered phenomenon: the fastest paths of information diffusion are supported by near gossip at the beginning and end and by far gossip in between to reach global coverage.
This occurs as long as faraway connections are permitted by the topology setup, whether they are explicitly planned as a hierarchy or not.

## Requirements

- Rust toolchain
- Cargo package manager
