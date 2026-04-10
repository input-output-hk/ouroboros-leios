# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build & Test Commands

```sh
cargo build --release          # build (release has debug symbols enabled)
cargo test                     # run all tests (this is what CI runs)
cargo test -p sim-core         # test only the core library
cargo test clock               # run tests matching "clock"
cargo clippy                   # lint
cargo run --release -- [topology.yaml] [output.jsonl] -s 100 -p parameters/linear.yaml
```

Rust toolchain: **1.88** (edition 2024). CI runs on Ubuntu 22.04.

## Running the Simulator

The `sim-cli` binary takes a topology YAML, optional output path, and flags:
- `-p <file>` — parameter overrides (layered via figment on top of `parameters/config.default.yaml`)
- `-s <n>` — number of slots to simulate
- `--trace-node <id>` — enable per-node tracing
- `-c` — conformance events mode
- `-a` — aggregate events mode

Without a topology argument, it searches default paths including `../../data/simulation/topo-default-100.yaml`.

## Architecture

Two-crate workspace: **sim-core** (library) and **sim-cli** (binary).

### Simulation Engines

Two engines selected by `engine` parameter (default: `actor`):

- **`actor`** — tokio-based async actor system. Each node runs as a tokio task coordinated by a virtual clock (`sim-core/src/sim/actor.rs`). Non-deterministic due to async scheduling. Supports adversarial scenarios.
- **`sequential`** — discrete event simulation (DES) processing events in strict timestamp order (`sim-core/src/sim/sequential.rs`). Deterministic. Uses rayon to parallelise simultaneous events across nodes within each timestep (BSP). Does not support attacker configs.

### Sharding

Nodes can be partitioned into shards for parallel execution. Both engines support sharding. Configured via:
- `shard-count` — number of shards (default: 1)
- `shard-strategy` — how nodes are assigned: `round-robin`, `zero-latency-clusters` (recommended), `geographic`, `min-latency-clusters`, `min-cut`

Shard assignment: `sim-core/src/sharding.rs`. For fast runs, use `-p parameters/turbo.yaml` (sequential engine, 6 shards, zero-latency-clusters).

### Virtual Clock (Actor Engine)

- **`ClockCoordinator`** — priority queue of wake-up times; advances time only when ALL actors are waiting and no tasks are in-flight
- **`ClockBarrier`** — per-actor handle; `wait_until(ts)` suspends the actor; `start_task()`/`finish_task()` prevent premature time advancement
- **`Timestamp`** — can be quantized to configurable resolution to batch simultaneous events

### Node Implementation Pattern

All node variants implement `NodeImpl` trait (`sim-core/src/sim/node.rs`), which defines handlers for: new slots, incoming transactions, network messages, CPU task completions, timed events, and custom events. Each handler returns `EventResult` carrying outgoing messages, CPU tasks, and future timed events.

`NodeDriver<N>` (`sim-core/src/sim/driver.rs`) wraps a `NodeImpl` in a tokio task with a `BinaryHeap<FutureEvent>` event loop that selects on network messages, transactions, and timed events.

### Leios Variants

Three node implementations selected by `config.variant`:

| Module | Variants |
|---|---|
| `sim/leios.rs` | `Short`, `Full`, `FullWithTxReferences` |
| `sim/stracciatella.rs` | `FullWithoutIbs` (EBs reference TXs directly) |
| `sim/linear_leios.rs` | `Linear`, `LinearWithTxReferences` |

`Simulation::new()` in `sim-core/src/sim.rs` dispatches on variant to construct the appropriate node types.

### Network Layer

`NetworkCoordinator` (`sim-core/src/network/`) runs as its own actor. `Connection<TProtocol, TMessage>` models per-link bandwidth (fair-shared across active mini-protocols: Tx, Block, IB, EB, Vote) and per-direction latency.

### CPU Task Simulation

`CpuTaskQueue<T>` (`sim-core/src/sim/cpu.rs`) models multi-core CPU contention — tasks split into subtasks, with optional core count limiting parallelism.

### Configuration

- **Topology** — YAML file defining nodes (stake, location, CPU cores) and link properties
- **Parameters** — layered YAML via figment; defaults at `parameters/config.default.yaml`; schema at `parameters/config.schema.json`
- Adversarial configs: `late_eb_attack`, `late_tx_attack`, `ib_equivocation`

### Event Tracking

`EventTracker` (`sim-core/src/events.rs`) sends all simulation events through an mpsc channel. `EventMonitor` in sim-cli consumes them, computes stats (liveness, diffusion timing, bandwidth), and writes `.jsonl` or `.cbor.gz` output.

### Lottery/VRF

`LotteryConfig::run()` (`sim-core/src/sim/lottery.rs`) uses stake-weighted randomness. Tests use `MockLotteryResults` with pre-filled deterministic outcomes.

## Test Structure

- Clock semantics: `sim-core/src/clock/coordinator.rs`
- CPU scheduling: `sim-core/src/sim/cpu.rs`
- Network connections: `sim-core/src/network/connection.rs`
- Linear Leios integration tests: `sim-core/src/sim/tests/linear_leios.rs` (uses `MockClockCoordinator` and `MockLotteryResults`)
- Topology parsing: `sim-cli/src/main.rs` (parses all files in `test_data/`)
- Test data generator: `sim-cli/src/bin/gen-test-data/`
