# net-cluster

Cluster orchestrator that spawns multiple `net-node` instances with auto-generated random topology, receives their telemetry via HTTP, and produces a merged time-ordered JSONL event log.

## Features

- Two topology sources: **random graph** (`[topology_source] type =
  "random"` with `num_nodes` / `degree` / `min_latency_ms` /
  `max_latency_ms` / `stake_distribution` inside the same table) or
  **YAML** (`type = "yaml"` with `path` + optional `node_limit`, loading
  `data/simulation/pseudo-mainnet/topology-v*.yaml` — same schema as
  `sim-rs` and `topology-checker`)
- Schema-level mode separation: random-mode fields under `type = "yaml"`
  (or vice versa) are rejected at parse time, not silently ignored
- Stake distribution: `"equal"` or `"mainnet-shaped"` (random mode) —
  taken directly from the YAML's `stake` field (YAML mode)
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
├── raw_topology.rs # YAML topology parser (v3/v4 schema)
└── types.rs      # StatsSnapshot (Deserialize), IngestedEvent, event parsing
```

## Usage

### Random topology (default)

```sh
# Build the net-node binary first (net-cluster spawns it as child processes):
cargo build -p net-node

# Run a 25-node cluster with sample config:
RUST_LOG=info cargo run -p net-cluster -- \
  --config net-cluster/configs/sample-cluster.toml \
  --net-node-bin target/debug/net-node

# Override settings (note dotted-key form — random-mode knobs live
# under `[topology_source]`):
cargo run -p net-cluster -- \
  --config net-cluster/configs/sample-cluster.toml \
  --net-node-bin target/debug/net-node \
  --set topology_source.num_nodes=10 --set topology_source.degree=3

# Ctrl-C to stop. Check merged event output:
cat cluster-events.jsonl | python3 -m json.tool --no-ensure-ascii | head

# Node logs are in logs/node-{i}.log
```

### YAML topology (mainnet-faithful)

Drive the cluster from a pre-built [`topology-v*.yaml`](../../data/simulation/pseudo-mainnet/)
file instead of generating a random graph. Same schema as `sim-rs` and
`topology-checker`, so the same files work across all three tools.

Mapping from YAML → cluster:

| YAML field | Cluster effect |
|------------|----------------|
| `nodes[].stake` | Node's stake (drives VRF block-production lottery) |
| `nodes[].producers[].latency-ms` | Per-link simulated delay (clamped to ≥0, rounded to whole ms) |
| `nodes[].producers[].bandwidth-bytes-per-second` | Parsed but currently ignored (no per-peer shaping yet) |
| `nodes[].region`, `.cpu-core-count`, etc. | Ignored — net-core has no notion of geography or CPU caps |

`num_nodes`/`degree`/`min_latency_ms`/`max_latency_ms`/
`stake_distribution` are the random-mode knobs and only exist inside
`[topology_source]` when `type = "random"`.  Writing them under
`type = "yaml"` is a **parse-time error** — the schema enforces the
split rather than silently ignoring leftover fields.  In YAML mode node
count comes from the YAML (optionally capped by `node_limit`), edges
and per-link latencies come from the YAML's `producers` arrays, and
per-node stake comes from the YAML's `stake` field.

```toml
# net-cluster/configs/sample-cluster-v4-mini.toml
base_config = "net-node/configs/mainnet.toml"
base_port = 30000
seed = 42
output_events = "cluster-v4-events.jsonl"
aggregator_port = 9100
stats_interval_secs = 2
rb_generation_probability = 0.05     # mainnet Praos f_block
tx_rate = 1.0

[topology_source]
type = "yaml"
path = "../data/simulation/pseudo-mainnet/topology-v4-mainnet.yaml"
node_limit = 25                      # first-N in YAML = top-N by stake in v4
```

```sh
cargo build -p net-node --release
RUST_LOG=info cargo run -p net-cluster --release -- \
  --config net-cluster/configs/sample-cluster-v4-mini.toml \
  --net-node-bin target/release/net-node
```

**Sizing:** `node_limit` controls memory + CPU footprint linearly.
v4-mainnet has 2,685 nodes with a dense peer graph — running it in
full as a process-per-node cluster will saturate any workstation.
Rule of thumb on a stock laptop: ~50 nodes on 16 GB RAM, ~250 on 48 GB.

`node_limit = 0` is rejected at startup (an empty cluster would boot
and idle silently); omit the field to load every node from the YAML,
or set a positive integer to cap at top-N by stake.

## Config

Key fields in the cluster TOML config:

| Field | Description |
|-------|-------------|
| `[topology_source]` | Optional topology selector.  `type = "random"` takes `num_nodes`, `degree`, `min_latency_ms`, `max_latency_ms`, `stake_distribution` (`"equal"` or `"mainnet-shaped"`). `type = "yaml"` takes `path` and optional `node_limit` (cap to top-N by stake). The schema rejects fields from the wrong variant at parse time. |
| `base_config` | Path to shared net-node base config |
| `base_port` | Starting port for node allocation |
| `seed` | RNG seed for reproducible topologies |
| `output_events` | Path for merged JSONL output |
| `ordering_window_secs` | Watermark window for time-ordered merge |
| `aggregator_port` | HTTP port for telemetry collection |
| `stats_interval_secs` | Periodic stats reporting interval |
| `rb_generation_probability` | Per-slot RB lottery rate override (applied to every node) |
| `tx_rate` | Per-node Poisson transaction generation rate (tx/s) |
| `behaviour` / `behaviour_selection` | Optional adversarial behaviour + which nodes run it |
| `external_peers` | Additional peers outside the cluster |

See `configs/sample-cluster.toml` for a random-mode example and
`configs/sample-cluster-v4-mini.toml` for a YAML-mode example.
