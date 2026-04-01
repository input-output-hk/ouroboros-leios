# net-node

Configurable Leios-capable test node for local network simulation. Uses TOML config files layered left-to-right, with `--set key=value` for individual overrides.

## Features

- VRF-based block production (stake-weighted lottery ported from sim-rs)
- Longest-chain consensus with fork-tracking chain tree
- Configurable fake validation with timed delays
- Leios IB/EB/vote production at stage boundaries
- Per-peer network delay injection for topology simulation
- Tx pool with fake Poisson transaction generation
- Telemetry: sim-rs-compatible JSONL events, per-peer bandwidth tracking
- Dual sinks: JSONL file output + HTTP POST to aggregator (for net-cluster)
- TOML config with figment layering (base + per-node overlays + CLI overrides)

## Structure

```
src/
├── main.rs         # CLI (clap), config loading, main event loop
├── config.rs       # TOML config structs (serde), figment layering, CLI overrides
├── clock.rs        # Slot clock: wall-clock -> slot mapping, aligned tick stream
├── network.rs      # Coordinator wrapper: config translation, peer setup, delay injection
├── production.rs   # VRF lottery (from sim-rs), fake Shelley+ block/EB/vote building
├── consensus.rs    # Longest-chain selection, Leios EB/vote fetch decisions
├── chain_tree.rs   # Fork-tracking tree structure for block headers, UI snapshots
├── validation.rs   # Fake validation with configurable timed delays
├── mempool.rs      # Tx pool + fake Poisson tx generation
└── telemetry.rs    # EventSink/StatsSink traits, JSONL file sink, HTTP sinks, peer stats
```

## Usage

```sh
# Two-node local test network (run in separate terminals):
RUST_LOG=info cargo run -p net-node -- \
  --config net-node/configs/mainnet.toml \
  --config net-node/configs/node0.toml

RUST_LOG=info cargo run -p net-node -- \
  --config net-node/configs/mainnet.toml \
  --config net-node/configs/node1.toml

# Fast slots for quick testing:
cargo run -p net-node -- \
  --config net-node/configs/mainnet.toml \
  --config net-node/configs/node0.toml \
  --set slot_duration_ms=200

# Check JSONL telemetry output:
cat node0-events.jsonl | python3 -m json.tool
```

## Config Layering

Config files are merged left-to-right via figment: base config (shared genesis, magic, protocol params) + per-node overlay (node_id, listen_address, peers, stake, telemetry). `--set key=value` overrides individual fields.

See `configs/` for examples:
- `mainnet.toml` — shared base config (magic, slot duration, protocol params)
- `node0.toml` / `node1.toml` — per-node overlays (node_id, listen_address, peers, stake)

## Telemetry

Events are emitted in sim-rs-compatible JSONL format:

```json
{"time_s":62969194.0,"message":{"type":"RBGenerated","node":"node-0","slot":125938388,"size_bytes":401}}
{"time_s":62969194.5,"message":{"type":"EBGenerated","node":"node-0","slot":125938390}}
```

Periodic stats (logged and/or POSTed to HTTP endpoint) include per-peer bandwidth:

```
periodic stats node=node-0 slot=100 tip=Some(50) produced=5 received=45 peers=1
  peer stats peer=peer-0 address=127.0.0.1:30001 mode=Duplex rtt_ms=None delay_ms=0 sent=1024 received=2048
```
