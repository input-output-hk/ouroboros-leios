# Plan for Test Node

The current CLI provides 'serve' and 'multi-follow' commands which exercise
a lot of the protocol functionality, but we want to move beyond this into
a prototype node which integrates both directions and can work within a test
network.

## Node requirements

- Provide a mini protocol endpoint for Praos & Leios combined
- Manage a set of peers using the multi-peer coordinator
- Inject fake transactions (similar to 'serve' currently)
- Inject fake blocks on a VRF schedule (see sim-rs in this repo for an implementation) based on a configured stake share
- Basic consensus, follow longest chain, select EBs to fetch - requires fleshing out.
- Fake block and transaction validation, with configurable timing factors (see sim-rs again)
- Injection of network delays to certain peers (allow network simulation on a local machine)

## Structure

The node should live in net-rs/net-node.  It it can be a single layer of major units - network.rs, production.rs, consensus.rs, validation.rs etc. to start with.  Keep it simple.

## Configuration

Configuration should be via TOML files, with the option to overlay deltas on top of a base file.  There should also be an option to set individual configuration properties on the command line.

## Telemetry

The node should record events and statistics, with configurable and pluggable
EventSink and StatsSinks.  Event sinks include:

- File - same format as sim-rs generates
- POST to a REST service - there will be a separate cluster aggregator that can receive them
- ... future ...

StatsSinks include

- Periodic logging
- POST to a REST service as above

## Out of scope

We will not validate or produce real blocks yet - there is a future potential
to merge this with [Acropolis](https://github.com/input-output-hk/acropolis)
to do so.  This should be borne in mind when creating reusable functionality.

## Implementation plan

### Crate structure

New crate: `net-rs/net-node/` added to workspace. Flat module layout:

```
net-node/src/
  main.rs          -- CLI (clap), config loading, node bootstrap, main event loop
  config.rs        -- TOML config structs (serde), figment layering, CLI overrides
  clock.rs         -- Slot clock: wall-clock -> slot mapping, aligned tick stream
  network.rs       -- Coordinator wrapper: config translation, peer setup, delay injection
  production.rs    -- VRF lottery, fake block/EB/vote building
  consensus.rs     -- Longest-chain selection, Leios EB fetch decisions
  validation.rs    -- Fake validation: configurable timed delays
  mempool.rs       -- Tx pool + fake tx generation
  telemetry.rs     -- EventSink/StatsSink traits + file/HTTP/log implementations
```

### Decisions

- **Block content:** Opaque random CBOR bytes (like serve.rs). No mempool tx inclusion for now.
- **Bootstrap:** Shared base TOML with per-node overlays via repeatable `--config`. A separate `net-cluster` orchestrator will handle spinning up multi-node networks with variant configs (future crate).
- **Delay model:** Inbound-only event delay via `DelayedEventStream`. No coordinator changes needed.
- **Event format:** Match sim-rs JSONL field names/structure for direct tooling reuse.
- **CLI:** `net-node --config base.toml --config node0.toml --set slot_duration_ms=100`. `--config` is repeatable, files layered left-to-right. `--set` for individual key=value overrides.

### Stage 1: Skeleton + Config + Slot Clock — COMPLETE

**Goal:** Running binary that loads layered TOML config, starts coordinator in duplex mode, connects to peers, accepts inbound, ticks slots.

**Modules:** `main.rs`, `config.rs`, `clock.rs`, `network.rs`

**Config schema (initial):**
```toml
node_id = "node-0"
listen_address = "0.0.0.0:3001"
network_magic = 764824073
slot_duration_ms = 1000
genesis_time_unix = 1710000000
seed = 42  # optional, omit for entropy
leios_enabled = true
scheduler = "priority-wfq"

[[peers]]
address = "127.0.0.1:3002"
```

**Config loading:** `figment` with TOML providers. Layer order: compiled defaults -> config files in order -> `--set` overrides.

**Slot clock:** Computes slot as `(now - genesis_time) / slot_duration`. Produces `tokio::time::interval_at` aligned to next slot boundary. Recomputes from wall clock each tick (no drift accumulation).

**Network wrapper:** Converts `NodeConfig` -> `CoordinatorConfig`, calls `spawn_coordinator`, issues `AddPeer` for configured peers.

**Main event loop:**
```rust
loop { tokio::select! {
    _ = slot_tick.tick() => { log slot }
    Some(event) = events.recv() => { log event }
    _ = shutdown => { break }
}}
```

**Verify:** Two nodes on different ports, each peering with the other. Confirm `PeerConnected` events and slot ticks at correct rate.

### Stage 2: Block Production + Transaction Injection — COMPLETE

**Goal:** Node produces fake Praos blocks via VRF lottery per slot. Generates and disseminates fake transactions.

**Modules:** `production.rs`, `mempool.rs`, extend `config.rs`

**Config additions:**
```toml
[production]
stake = 100
total_stake = 1000
rb_generation_probability = 0.05

[transactions]
tx_rate = 1.0          # txs/sec, Poisson
tx_size_min = 250
tx_size_max = 16384
```

**VRF lottery:** Port `compute_target_vrf_stake` from `sim-rs/sim-core/src/sim/lottery.rs`. Per slot: generate random u64, compare against `(stake / total_stake) * probability * total_stake`. On win, build fake block (random hash, correct slot, opaque CBOR body -- same pattern as `serve.rs`), send `InjectBlock`.

**Mempool:** Background task with Poisson timer. Generates random tx bodies, submits via `SubmitTransaction`. Also receives `TransactionReceived` events and buffers them.

**Verify:** Single node with `stake = total_stake` produces every slot. Second node following sees blocks via ChainSync. Deterministic seed gives reproducible sequence.

### Stage 3: Consensus + Validation — COMPLETE

**Goal:** Follow longest chain from peers, fetch blocks, validate with configurable delays, re-serve validated blocks.

**Modules:** `consensus.rs`, `validation.rs`, extend `config.rs`

**Config additions:**
```toml
[validation]
rb_head_validation_ms = 1.0
rb_body_validation_ms_constant = 5.0
rb_body_validation_ms_per_byte = 0.001
tx_validation_ms = 0.5
```

**Consensus:** Track `local_tip`. On `TipAdvanced` with higher `block_no`, issue `FetchBlock`. On `BlockReceived`, submit to validation. On validation complete, `InjectBlock` to serve downstream + update `local_tip`. On `RolledBack`, issue `InjectRollback` and reset tip.

**Validation:** `tokio::spawn` a sleep task for `constant + per_byte * body.len()`, sends completion on mpsc channel. Main loop has a `validation_rx` arm in select.

**Verify:** Node A produces, Node B follows with 500ms validation delay. Measure lag. Two producers with 50/50 stake, follower tracks longest chain across forks.

### Stage 4: Leios Production + Network Delay Injection — COMPLETE

**Goal:** Extend production/consensus to Leios (IBs, EBs, votes). Add delay injection for simulation.

**Modules:** extend `production.rs`, `consensus.rs`, `validation.rs`, `network.rs`, `config.rs`

**Config additions:**
```toml
[production]
ib_generation_probability = 0.5
eb_generation_probability = 0.5
vote_generation_probability = 0.8
stage_length_slots = 20

[validation]
eb_validation_ms = 2.0
vote_validation_ms = 1.0

[[peers]]
address = "127.0.0.1:3003"
inbound_delay_ms = 200
```

**Leios production:** At stage boundaries (`slot % stage_length == 0`), run EB and vote lotteries. Per slot, run IB lottery. Inject via `InjectLeiosBlock`/`InjectLeiosVotes`.

**Leios consensus:** On `LeiosBlockOffered` -> `FetchLeiosBlock`. On `LeiosVotesOffered` -> `FetchLeiosVotes`. Track EB/vote state for production decisions.

**Delay injection:** Implemented inside the coordinator via `peer_delays: HashMap<String, Duration>` config. Events from peers with configured delays are buffered and delivered after the specified duration. Per-peer granularity, zero overhead when unconfigured. Configured via `inbound_delay_ms` on `[[peers]]` entries.

**Verify:** Three-node triangle with Leios enabled. Verify EB/vote propagation. Measure delay injection effect on block reception timing.

### Stage 5: Telemetry — COMPLETE

**Goal:** Event and stats sinks for observability. File format compatible with sim-rs tooling.

**Modules:** `telemetry.rs`, extend `config.rs`, wire into `main.rs`

**Config additions:**
```toml
[telemetry]
stats_interval_secs = 10

[[telemetry.event_sinks]]
type = "file"
path = "events.jsonl"

[[telemetry.event_sinks]]
type = "http"
url = "http://localhost:8080/events"

[[telemetry.stats_sinks]]
type = "log"
```

**Events:** JSONL format with `{timestamp, node_id, slot, ...kind}`. Types: `BlockProduced`, `BlockReceived`, `BlockValidated`, `TipAdvanced`, `RolledBack`, `EbProduced`, `VoteProduced`, `TxGenerated`. Match sim-rs field names/structure for tooling reuse.

**Stats:** Periodic snapshot: `{uptime, slot, tip_block_no, blocks_produced/received/validated, txs, peer_count}`.

**Sinks:** `FileEventSink` (buffered JSONL), `HttpEventSink` (batched POST), `LogStatsSink` (tracing::info on interval), `HttpStatsSink` (periodic POST).

**Verify:** Run node with file sink, verify JSONL output. Feed into sim-rs analysis tooling.

### Risks

- **Coordinator `.send().await` blocking:** Main loop must drain events promptly. Validation is non-blocking (spawned tasks). Telemetry sinks must buffer/drop, never block.
- **Clock drift:** Mitigated by recomputing slot from wall clock each tick, not incrementing a counter.
- **Leios stage alignment:** Deterministic from `slot / stage_length_slots` -- all nodes with same config agree.
- **Self-produced block re-fetch:** When the node produces and injects a block, the coordinator announces it to peers who may announce it back. Consensus module must track "I produced this point" to avoid re-fetching own blocks.
- **Fake block CBOR parsability:** Downstream nodes may try to parse headers via `WrappedHeader::parse()`. Fake CBOR needs correct Shelley+ array structure with valid slot values, not just random bytes.

### Future: net-cluster Orchestrator

After net-node is complete, a `net-cluster` crate will orchestrate multi-node test networks -- generating configs from base TOML + per-node variants, launching processes, and coordinating genesis.
