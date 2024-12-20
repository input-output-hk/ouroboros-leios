# Network Topology Analysis

This directory contains topology analyses for networks of varying sizes and
configurations. The analysis helps evaluate network connectivity and stake
distribution patterns through metrics and visualizations.

## Small Network

**Network Overview:**

- 20 Producer nodes
- 30 Relay nodes
- Average relay connections: 1.4

No significant issues detected.
[View detailed metrics](small/topology_issues.md)

![Network Metrics](small/topology_metrics.png)

## Medium Network

**Network Overview:**

- 50 Producer nodes
- 50 Relay nodes
- Average relay connections: 3.2

7 nodes with connectivity issues identified.
[View detailed metrics](medium/topology_issues.md)

![Network Metrics](medium/topology_metrics.png)

## Realistic Network

**Network Overview:**

- 1960 Producer nodes
- 1040 Relay nodes
- Average relay connections: 4.7

6 nodes with connectivity issues identified.
[View detailed metrics](realistic/topology_issues.md)

![Network Metrics](realistic/topology_metrics.png)

## Thousand-Node Network

**Network Overview:**

- 50 Producer nodes
- 950 Relay nodes
- Average relay connections: 11.2

7 nodes with connectivity issues identified.
[View detailed metrics](thousand/topology_issues.md)

![Network Metrics](thousand/topology_metrics.png)

## Visualization Guide

The topology metrics plot shows:

- X-axis: Number of relay connections per producer
- Y-axis: Node stake (log scale)
- Color: Number of other producers reachable through direct relay connections
  (1-hop)
