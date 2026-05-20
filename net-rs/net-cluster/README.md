# net-cluster

Cluster orchestrator that spawns multiple `net-node` instances with auto-generated random topology, receives their telemetry via HTTP, and produces a merged time-ordered JSONL event log.

## Features

- Random graph topology generation with configurable degree and edge delays
- Stake distribution: equal, weighted, or zipf
- Per-node TOML overlay generation (ports, peers, delays, stake)
- Child process management with graceful shutdown
- HTTP telemetry server (POST /events, POST /stats)
- Time-ordered event merge with watermark-based flushing
- Merged JSONL output for downstream analysis / visualization
- Per-node log capture to `logs/node-{i}.log`

## Structure

```
src/
├── main.rs       # CLI (clap), orchestration flow, signal handling
├── config.rs     # ClusterConfig, figment loading
├── topology.rs   # Random graph generation, port allocation, edge delays, stake
├── overlay.rs    # Per-node TOML overlay generation, temp file management
├── process.rs    # Child process spawning, shutdown, log piping
├── server.rs     # axum HTTP server: POST /events, POST /stats
├── aggregator.rs # Time-ordered event merge, watermark flushing, JSONL output
└── types.rs      # StatsSnapshot (Deserialize), IngestedEvent, event parsing
```

## Usage

```sh
# Build the net-node binary first (net-cluster spawns it as child processes):
cargo build -p net-node

# Run a 5-node cluster with sample config:
RUST_LOG=info cargo run -p net-cluster -- \
  --config net-cluster/configs/sample-cluster.toml \
  --net-node-bin target/debug/net-node

# Override settings:
cargo run -p net-cluster -- \
  --config net-cluster/configs/sample-cluster.toml \
  --net-node-bin target/debug/net-node \
  --set num_nodes=10 --set degree=3

# Ctrl-C to stop. Check merged event output:
cat cluster-events.jsonl | python3 -m json.tool --no-ensure-ascii | head

# Node logs are in logs/node-{i}.log
```

## Config

Key fields in the cluster TOML config:

| Field | Description |
|-------|-------------|
| `num_nodes` | Number of nodes to spawn |
| `degree` | Peers per node in the random graph |
| `min_latency_ms` / `max_latency_ms` | Random edge delay range |
| `base_config` | Path to shared net-node base config |
| `base_port` | Starting port for node allocation |
| `seed` | RNG seed for reproducible topologies |
| `output_events` | Path for merged JSONL output |
| `ordering_window_secs` | Watermark window for time-ordered merge |
| `aggregator_port` | HTTP port for telemetry collection |
| `stake_distribution` | `"equal"`, `"weighted"`, or `"zipf"` |
| `stats_interval_secs` | Periodic stats reporting interval |
| `external_peers` | Additional peers outside the cluster |

See `configs/sample-cluster.toml` for a complete example.
