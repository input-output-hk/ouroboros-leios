# Net-rs test cluster plan

The test-node is a single node instance which can be configured from a base
template with a given stake share and network peers.  We need a method to
spin up multiple of these and capture their event and stats logging.  Then
we will need a UI to diagram the cluster and show statistics graphs etc.

## Cluster aggregator

A new Rust server in net-rs/net-cluster which can spawn net-node instances
with overlay configs from a common base config.  It should have its own
config.toml.

Given a target number of node instances, it should allocate localhost ports
and then associate peers randomly, according to a degree config.

It should also have a mechanism to inject external peers into that mix as well, allowing running multiple clusters in different locations for real network
measurement.

Latency of the edges should be randomised between a configurable min and max for each edge.

## REST servers

It should provide a REST endpoint for telemetry data from the nodes and aggregate event logs into a time-ordered series, which it logs to a file (sim-rs event log format again) and also keeps a window of N seconds of events.  It will need to use the window to ensure time ordering of the output - it can only write up to the earliest last event for any node.

The latest statistics should be kept for each node as well.

It should also provide a separate endpoint for a UI to query for:

1) Network topology - a list of nodes and edges
2) Latest statistics for all nodes and individual nodes
3) All events after time T

The server should provide a Swagger definition (OpenAPI.yaml) of its UI endpoints, and copy the run-local-swagger.sh from sim-rs to run it in Docker.

Later we will add control endpoints to (e.g.) start and stop individual nodes,
break edges, set tx and block generation parameters etc.  Just allow room for
these in the REST server for now.

## UI

We will need a Vite+React+TypeScript+Zustand+MUI SPA in net-rs/net-ui which can:

1) Query the net-cluster for node/edge topology and display it.  Use ReactFlow and d3-force for automatic layout - see https://reactflow.dev/examples/layout/force-layout although that's a Pro feature - implement it directly with d3-force adjusting node positions.  Edges should be labelled with their latency.

2) Show a running log of the event stream - poll every second for new events after the last event time received.

3) Show rolling graphs of:

a) Total bandwidth consumed
b) Total messages sent
c) Total blocks produced
(to be extended)

Poll for all stats every second.

4) Show inspection graphs when any node or edge is selected showing its own rolling graphs of bandwidth, messages sent etc.

5) Show node details, peers and latest stats for each node when selected.

6) Layout:
 ----------------------------
|                 |          |
|                 | Inspector|
|   Node graph    | panel    |
|                 |          |
|                 |          |
 ----------------------------
|    Aggregate graphs        |
|                            |
 ----------------------------

