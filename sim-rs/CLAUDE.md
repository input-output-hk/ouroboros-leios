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
- **`sequential`** — discrete event simulation (DES) processing events in strict timestamp order (`sim-core/src/sim/sequential.rs`). Deterministic (see below). Uses rayon to parallelise simultaneous events across nodes within each timestep (BSP). Does not support attacker configs.

### Sharding

Nodes can be partitioned into shards for parallel execution. Both engines support sharding. Configured via:
- `shard-count` — number of shards (default: 1)
- `shard-strategy` — how nodes are assigned: `round-robin`, `zero-latency-clusters` (recommended), `geographic`, `min-latency-clusters`, `min-cut`

Shard assignment: `sim-core/src/sharding.rs`. For fast runs, use `-p parameters/turbo.yaml` (sequential engine, 6 shards, zero-latency-clusters).

### Determinism

The sequential engine (including multi-shard turbo) produces bit-identical results across runs with the same seed/config. This required fixing several non-obvious sources of non-determinism:

1. **HashMap iteration** — Node state in `linear_leios.rs` uses `BTreeMap`/`BTreeSet` (not `HashMap`/`HashSet`) for all fields that could be iterated. Remaining `HashSet` usages are pure membership tests (contains/insert) and are noted as such. The `praos` state and `Connection` bandwidth queues were already `BTreeMap`.

2. **Shard assignment** — Sharding strategies (`zero_latency_clusters`, `min_latency_clusters`, `min_cut`) use `BTreeMap` to collect components so that component ordering is deterministic. The component sort has a stable tiebreaker (first NodeId) for same-size components.

3. **TX ID assignment** — `TxGeneratorCore` uses per-shard local counters (offset by `shard_index * 1B`) instead of shared `AtomicU64` counters, so ID assignment doesn't depend on cross-shard thread scheduling.

4. **Rayon indexed collect** — The rayon parallel dispatch in `sequential.rs` uses `.map()` (not `.filter().map()`) to keep the iterator indexed, ensuring `collect()` preserves node order regardless of work-stealing schedule.

5. **Cross-shard delivery** — The CMB (Conservative Message-Based) protocol delivers cross-shard messages sorted by `(send_time, source_shard, seq)` via a priority queue. Combined with the above fixes, this is deterministic without requiring barrier synchronization between shards.

6. **Event stream sorting** — The event monitor buffers events in timestamp buckets with a 1-second window and sorts each bucket by originating node ID before writing, making `.jsonl` output byte-identical across runs even though shard threads emit tracking events concurrently.

**What does NOT affect determinism**: `CpuTaskQueue` HashMap (keyed by monotonic task_id, only accessed by key lookup), `pending_deliveries` HashSet (only contains/insert/remove), config-level HashSets (`vote_eligible_nodes`, `attackers` — only contains checks).

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

## Benchmark Scripts

### cip-voting-options.sh

Runs voting/certification benchmarks across throughput levels, committee modes, and seeds.

```sh
# Basic usage (all defaults: turbo engine, 1500 slots, seed 0)
./scripts/cip-voting-options.sh

# Single config
./scripts/cip-voting-options.sh -T 0.350 -m everyone -S 0

# Multiple seeds
./scripts/cip-voting-options.sh -T 0.200 -m wfa-ls -S 0,1,2,3,4

# With event stream capture (jsonl)
./scripts/cip-voting-options.sh -T 0.350 -m everyone -S 0 -o /tmp/events

# Custom label and extra params
./scripts/cip-voting-options.sh -T 0.350 -m everyone -S 0 -L my-test -P /tmp/override.yaml
```

Key flags: `-T` throughput, `-m` committee mode (`wfa-ls`, `everyone`, `top-stake-fraction`), `-e` engine (`turbo`, `sequential`, `actor`), `-S` seeds (comma-separated), `-L` label for CSV rows, `-P` extra parameter YAML (repeatable), `-o` output directory for `.jsonl` event streams, `-s` slots (default 1500).

Results are appended to `voting_results.csv`. Per-run sim logs go to `/tmp/sim-T{throughput}-{mode}-{engine}-seed{seed}.log`.

### poll-sim.sh

Monitor a running benchmark:
```sh
./scripts/poll-sim.sh /tmp/sim-T0.350-everyone-turbo-seed0.log
```
Shows process status (PID, elapsed, CPU%, RSS) and recent log output.

### Determinism verification

To verify turbo determinism, run the same config twice and compare:
```sh
# Summary stats (should match exactly except wall-clock time):
./scripts/cip-voting-options.sh -e turbo -T 0.350 -m everyone -S 0 -L run1
./scripts/cip-voting-options.sh -e turbo -T 0.350 -m everyone -S 0 -L run2
grep 'run[12]' voting_results.csv

# Byte-identical event streams:
./scripts/cip-voting-options.sh -e turbo -T 0.350 -m everyone -S 0 -L a -o /tmp/det -s 100
./scripts/cip-voting-options.sh -e turbo -T 0.350 -m everyone -S 0 -L b -o /tmp/det -s 100
cmp /tmp/det/T0.350-everyone-turbo-seed0-a.jsonl /tmp/det/T0.350-everyone-turbo-seed0-b.jsonl
```

**Performance notes**: Turbo at 0.350 throughput / 750 nodes / 1500 slots takes ~15 min and ~28GB RSS. The `.jsonl` event stream adds ~15GB memory (unbounded mpsc buffering) and ~60GB disk per run. Do not run two benchmarks simultaneously — they compete for CPU and memory.

## Test Structure

- Clock semantics: `sim-core/src/clock/coordinator.rs`
- CPU scheduling: `sim-core/src/sim/cpu.rs`
- Network connections: `sim-core/src/network/connection.rs`
- Linear Leios integration tests: `sim-core/src/sim/tests/linear_leios.rs` (uses `MockClockCoordinator` and `MockLotteryResults`)
- Topology parsing: `sim-cli/src/main.rs` (parses all files in `test_data/`)
- Test data generator: `sim-cli/src/bin/gen-test-data/`
