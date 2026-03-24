# net-rs Implementation Plan

## Context

net-rs is a greenfield Rust implementation of the Cardano mini-protocol network stack for
Praos and Leios. Structural decisions are informed by Leios requirements (QoS, priority
scheduling, new protocols) so we don't need to refactor later.

Key references (all in `docs/`): `praos-network.md` (protocol spec), `leios-changes.md`
(what Leios needs from the mux), `implementation-haskell.md` and
`implementation-pallas-v1.md` / `v2.md` (prior art).

## Architectural Layering

The design is layered to support both simple tool use and multi-peer node operation,
without the lower layers dictating the concurrency model.

### The problem: single-peer vs multi-peer coordination

Pallas v1 gives each connection independent protocol handles driven by `await` calls.
This works for tools (connect to one node, fetch data, disconnect) but breaks down when
you need to coordinate across peers — e.g. ChainSync on peer A announces a header, and
you need to BlockFetch it from peer B based on latency.

Pallas v2 solves this with an event-driven model (Interface/Behavior/Manager) where all
protocol messages from all peers flow through a single `handle_io()` callback. The
behavior layer has a unified view of all peer states.

The Haskell node takes a third approach: independent concurrent actors (one per protocol
instance) coordinating through shared mutable state (STM TVars for chain DB, mempool,
candidate chains) with a separate Peer Selection Governor making connection decisions.

### Our approach: layered, not opinionated

Rather than choosing one model upfront, we layer the architecture so that the core
protocol machinery is reusable under any concurrency model:

- **Layer 1 — net-core** (Phase 1-2): Protocol state machines, codecs, mux, bearer.
  No opinion on single-peer vs multi-peer. State machines are pure
  (`transition(state, msg) -> Result<State>`) — they can be driven by direct `await`
  calls or by an event loop.

- **Layer 2 — Connection API** (Phase 1-2): Single-connection facade —
  `connect()` → handshake → protocol handles. Simple, imperative, v1-style. Good for
  tools, tests, and the CLI.

- **Layer 3 — Coordinator** (Phase 3+): Multi-peer coordination. Thread-per-peer model
  with a shared coordinator task. Each peer runs an independent task tree; the coordinator
  aggregates state via `PeerHandle` channels and makes cross-peer decisions (fetch
  scheduling, promotion/demotion). Exposes a peer-agnostic interface upward (candidate
  chain tips, block requests, bad-peer reports).

The critical design constraint is that Layer 1's types must not preclude Layer 3. This
means:
- Protocol state machines must be pure (no embedded I/O or channel ownership)
- Channels must be splittable (`ChannelSend` + `ChannelRecv`) for pipelining
- Decoder state must be separate from the channel
- The `Protocol` trait should not assume request-response pairing

## Implementation Phases

### Phase 1: Mux + Handshake — COMPLETE

Deliverable: `net-cli` that connects to an existing Cardano node, completes handshake,
prints negotiated version. Also: server-side handshake and MemBearer integration tests.

Built: bearer trait (TCP + mem), mux (wire format, egress with scheduler, ingress with
`try_send` and shared `IngressCounter`, supervisor for error propagation), CBOR codec
with `max_buffer` and HRTB decode, protocol framework (`Runner` with agency checks),
handshake protocol (client + server + N2N negotiation), CLI with subcommands.

51 tests. Live-tested against backbone.cardano.iog.io:3001. Security audit completed:
segment size validation, CBOR collection caps, buffer limits, non-blocking demuxer,
mode bit validation, supervisor teardown.

Additions beyond original plan: supervisor task, IngressCounter, try_send in demuxer,
max_buffer in codec, CBOR collection length caps, capture command, test vectors from
live node, security audit checklist.

### Phase 2: ChainSync + BlockFetch — COMPLETE

Deliverable: persistent chain follower CLI that connects to mainnet, follows the tip,
handles rollbacks and reconnections. Fake server CLI for local testing.

Built: shared Cardano types (Point, Tip, WrappedHeader, BlockBody with CBOR encode/decode
and allocation bounds), ChainSync protocol (client helpers: find_intersection, request_next,
done; state machine with 5 states, 8 messages), BlockFetch protocol (client helpers:
request_range, recv_block, done; 4 states, 6 messages), KeepAlive protocol (keep_alive
client helper with cookie validation, ping/pong; 3 states, 3 messages).

Server: Runner-based with Message directly (no separate Request/Response types — Runner
enforces agency). Fake server (`serve` CLI) generates blocks on Poisson schedule with
configurable rollback rate/depth. Connection helper (`connect.rs`) with both client
(`connect_and_handshake`) and server (`accept_and_handshake`) variants.

CLI: `chain-sync` (debug, limited count), `block-fetch` (fetch tip block), `follow`
(persistent chain follower with reconnection, KeepAlive background task, intersection-based
resume, drain of initial re-delivery), `serve` (fake server with `--block-rate`,
`--rollback-rate`, `--max-rollback-depth`).

109 tests. Live-tested against backbone.cardano.iog.io:3001 and local fake server.
Security-audited (allocation bounds, buffer caps, timeouts, no panics, agency enforcement).

### Phase 3: Remaining Praos Protocols + Multi-Peer

#### Protocols — COMPLETE

All 6 N2N mini-protocols implemented. 147 total tests.

- **TxSubmission** (protocol ID 4) — pull-based tx dissemination with blocking/non-blocking
  modes. 6 states, 7 message types (MsgInit, MsgRequestTxIds blocking/non-blocking,
  MsgReplyTxIds, MsgRequestTxs, MsgReplyTxs, MsgDone). Flow control with ack/req windowing
  (max 10 unacked). Module-local types: TxId, TxBody, TxIdAndSize, PendingTx (opaque CBOR
  wrappers). Client helper `run_client` manages FIFO of announced txs, responds to server
  pulls via mpsc channel. CBOR codec with indefinite-length inner lists per Haskell codec.
  CLI `submit` command with single-tx and Poisson stream modes. 20 tests.
- **PeerSharing** (protocol ID 10) — request/reply for peer discovery. 3 states, 3 message
  types (MsgShareRequest, MsgSharePeers, MsgDone). PeerAddress type with IPv4/IPv6 support.
  Client helper `share_request`. CLI `peer-share` command with peer_sharing=1 handshake
  negotiation and graceful rejection. Live-tested against cardano-main2.everstake.one:3001.
  18 tests.

Server side: fake `serve` command handles all 6 protocols (ChainSync, BlockFetch,
TxSubmission, PeerSharing, KeepAlive) plus Handshake.

#### Multi-Peer Coordination — COMPLETE

Thread-per-peer model with a shared coordinator. InitiatorOnly + ResponderOnly peers.
171 total tests.

**Design decision (2026-03-24):** After evaluating three approaches — (1) thread-per-peer
with coordinator, (2) Pallas v2 event-driven single-threaded behavior, (3) Haskell-style
actor model — we chose option 1. The single-threaded nature of option 2 is undesirable.
Option 3's full actor constellation is over-engineered for ~20 peers. Option 1 extends the
existing per-connection task tree naturally, and the coordinator pattern (events up, commands
down via channels) handles all known coordination scenarios without architectural risk.

**Architecture (implemented):**

```
Application (multi-follow CLI, serve CLI)
    ↑ NetworkEvent (peer-agnostic: TipAdvanced, BlockReceived, TransactionReceived, ...)
    ↓ NetworkCommand (AddPeer, FetchBlock, InjectBlock, InjectRollback, Shutdown, ...)
Coordinator task (single tokio task)
    ├── ChainStore (Arc, shared with responder tasks)
    ├── Accept loop (if listen_address configured)
    ↑ (PeerId, PeerEvent) via shared mpsc fan-in from all peers
    ↓ PeerCommand via per-peer mpsc (FetchBlocks, RequestPeers, Disconnect)
InitiatorOnly Peer Tasks (outbound connections, client protocols)
    ├── ChainSync client (request_next loop → HeaderAnnounced/RolledBack)
    ├── BlockFetch client (idle, receives FetchBlocks → BlockFetched)
    ├── KeepAlive client (periodic pings → LatencyMeasured)
    └── PeerSharing client (on-demand → PeersDiscovered)
ResponderOnly Peer Tasks (inbound connections, server protocols)
    ├── ChainSync server (reads from ChainStore, serves headers)
    ├── BlockFetch server (reads from ChainStore, streams blocks)
    ├── KeepAlive server (echo)
    ├── TxSubmission server (pulls txs → TransactionReceived)
    └── PeerSharing server (serves peer addresses via callback)
```

**Key implementation details:**
- `PeerEvent` abstracts over raw protocol messages — peer task is the translation layer
- Coordinator deduplicates tips by block number (only forwards if ahead of best known)
- Fetch routing: picks peer with matching tip and lowest RTT
- Reconnection: exponential backoff (1s → 2s → 4s → ... → 30s cap) for initiator peers only
- `ConnectionMode` enum: `InitiatorOnly` and `ResponderOnly` implemented; `Duplex` deferred
- `ChainStore`: shared in-memory chain state (VecDeque with capacity eviction, watch::channel
  notification). Coordinator populates from `BlockFetched` events (with header from
  `pending_headers` map) and `InjectBlock` commands. Responder tasks read via `Arc<ChainStore>`.
- Server protocol handlers in `net-core::peer::server_handlers` — extracted from serve.rs,
  parameterized on `Arc<ChainStore>` and event senders
- Accept loop: spawned as background task if `listen_address` configured; feeds completed
  connections to coordinator via internal mpsc channel
- `serve` CLI refactored to use coordinator with `InjectBlock`/`InjectRollback` commands
- `multi-follow --listen` enables relay mode (initiator upstream + responder downstream)

**Deferred for future phases:**
- Promotion/demotion (warm/hot lifecycle, cancellation tokens per protocol group)
- Duplex mode (both initiator + responder protocols on one connection, Cardano V10+)
- Backoff reset on sustained connection success

**Live-tested:** Mainnet initiator peers with tip deduplication. Local relay chain:
serve → multi-follow (with --listen) → follow. Exponential backoff reconnection.

### Phase 4: Leios Protocols

Deliverable: LeiosNotify, LeiosFetch protocols. Priority scheduling and freshest-first
delivery in the coordinator.

Builds on the multi-peer coordinator from Phase 3:
- LeiosNotify/LeiosFetch state machines (same Runner pattern as all other protocols)
- Add to per-peer task trees as new protocol tasks
- Extend PeerHandle with Leios-specific events (EB announced, vote received)
- Freshest-first fetch scheduling in coordinator (priority hint on fetch requests)
- StrictPriority/WFQ scheduler in mux (StrictPriority already implemented)

## Workspace Structure

```
net-rs/
  Cargo.toml          -- workspace root
  net-core/
    Cargo.toml
    src/
      lib.rs
      bearer/
        mod.rs         -- Bearer trait
        tcp.rs         -- TcpBearer
        mem.rs         -- MemBearer (in-memory for tests)
      mux/
        mod.rs         -- Mux, RunningMux
        wire.rs        -- 8-byte header encode/decode, Segment type
        egress.rs      -- per-protocol egress queues + scheduler
        ingress.rs     -- demuxer + per-protocol ingress buffers
        channel.rs     -- ChannelSend / ChannelRecv (split halves)
        scheduler.rs   -- Scheduler trait + RoundRobin + StrictPriority
      codec.rs         -- IncrementalDecoder, CBOR framing over channel
      protocol.rs      -- Protocol trait, State, Agency, Message framework
      protocols/
        mod.rs
        handshake/
          mod.rs       -- state machine, messages
          codec.rs     -- CBOR encode/decode
          client.rs    -- client peer
          server.rs    -- server peer
          n2n.rs       -- N2N version data types
  net-cli/
    Cargo.toml
    src/
      main.rs          -- Phase 1 test CLI
```

## Layer Design

### Bearer (`bearer/`)

Trait-based, not enum. Each transport is a separate module for pluggability — adding a new
transport (QUIC, Unix socket, etc.) means adding a new file, not modifying existing code.

**`bearer/mod.rs`** — trait definition:
```rust
pub trait Bearer: Send + 'static {
    type Read: AsyncRead + Send + Unpin + 'static;
    type Write: AsyncWrite + Send + Unpin + 'static;
    fn split(self) -> (Self::Read, Self::Write);
}
```

**`bearer/tcp.rs`** — `TcpBearer` wrapping `tokio::net::TcpStream` with TCP_NODELAY +
keepalive. Provides `connect()`, `connect_timeout()`, `accept()`.

**`bearer/mem.rs`** — `MemBearer` using `tokio::io::duplex()` for unit/integration tests.
`MemBearer::pair() -> (MemBearer, MemBearer)` creates a connected pair.

### Mux (`mux/`)

Two tokio tasks (muxer + demuxer), per-protocol channels, pluggable scheduler.

**Wire format** (`wire.rs`): 8-byte header (big-endian), `Segment { header, payload }`.
Constants: `HEADER_LEN = 8`, `DEFAULT_SDU_SIZE = 12_288`.

**Egress** (`egress.rs`): Each registered protocol gets a bounded `mpsc` sender. The muxer
task pulls from protocol queues according to the `Scheduler`, fragments into SDUs, writes
to bearer.

**Ingress** (`ingress.rs`): Demuxer reads SDUs from bearer, dispatches to per-protocol
ingress buffers. Each buffer has a configurable byte limit. Overflow = connection error
(per spec).

**Channel** (`channel.rs`): `ChannelSend` + `ChannelRecv` — split halves from the start
for pipelining compatibility. Phase 1 uses them from a single task; Phase 2 can use them
from sender/receiver tasks.

**Scheduler** (`scheduler.rs`):
```rust
pub trait Scheduler: Send + 'static {
    fn next(&mut self, ready: &[ProtocolId]) -> Option<ProtocolId>;
    fn register(&mut self, id: ProtocolId, priority: Priority);
}
```
Implementations: `RoundRobin` (Phase 1 default), `StrictPriority` (for Leios).

**Mux public API**:
```rust
pub struct MuxConfig {
    pub sdu_size: u16,           // default 12_288
    pub protocols: Vec<ProtocolConfig>,  // id, direction, priority, ingress limit
}

pub struct RunningMux { /* JoinHandles for muxer + demuxer */ }

impl Mux {
    pub fn new(config: MuxConfig) -> Self;
    pub fn channel(&mut self, protocol: ProtocolId) -> (ChannelSend, ChannelRecv);
    pub fn run<B: Bearer>(self, bearer: B) -> RunningMux;
}
```

### Codec (`codec.rs`)

Wraps `ChannelSend`/`ChannelRecv` with CBOR framing. Handles the no-message-framing
problem by using minicbor's incremental decode.

```rust
pub struct CodecSend { channel: ChannelSend }
pub struct CodecRecv { channel: ChannelRecv, buffer: BytesMut }

impl CodecSend {
    pub async fn send<M: Encode>(&mut self, msg: &M) -> Result<()>;
}

impl CodecRecv {
    pub async fn recv<'a, M: Decode<'a>>(&'a mut self) -> Result<M>;
}
```

The `buffer` in `CodecRecv` accumulates bytes across segment boundaries and the decoder
consumes exactly what it needs. Decoder state is in `CodecRecv`, separate from the
channel — this is the pipelining-compatible design.

### Protocol Framework (`protocol.rs`)

Runtime agency checks. Define protocols via trait:

```rust
pub enum Agency { Client, Server, Nobody }

pub trait Protocol: Send + 'static {
    type State: Clone + Debug + Send;
    type Message: Encode + Decode + Debug + Send;

    fn agency(state: &Self::State) -> Agency;
    fn initial_state() -> Self::State;
    fn transition(state: &Self::State, msg: &Self::Message) -> Result<Self::State>;
    fn size_limit(state: &Self::State) -> usize;
    fn timeout(state: &Self::State) -> Option<Duration>;
}
```

Driver runs a protocol over a codec:

```rust
pub async fn run_client<P: Protocol>(
    codec: (CodecSend, CodecRecv),
    peer: impl ClientPeer<P>,
) -> Result<()>;

pub async fn run_server<P: Protocol>(
    codec: (CodecSend, CodecRecv),
    peer: impl ServerPeer<P>,
) -> Result<()>;
```

`ClientPeer`/`ServerPeer` traits define the business logic callbacks, similar to Pallas
v1's layered send/recv but with the framework handling agency checks and timeouts.

### Handshake (`protocols/handshake/`)

First concrete protocol. Validates the entire stack end-to-end.

- States: `StPropose`, `StConfirm`, `StDone`
- Messages: `MsgProposeVersions`, `MsgAcceptVersion`, `MsgRefuse`, `MsgQueryReply`
- N2N version data: `networkMagic`, `diffusionMode`, `peerSharing`, `query`
- Supports V14/V15
- Special: runs before mux is fully initialized (single-segment messages)
- Client: proposes versions, receives accept/refuse
- Server: receives proposal, runs negotiation algorithm, responds

### Connection (`lib.rs` or `connection.rs`)

High-level API tying it together:

```rust
pub async fn connect(addr: SocketAddr, magic: u32) -> Result<Connection>;
pub async fn accept(listener: &TcpListener, magic: u32) -> Result<Connection>;

pub struct Connection {
    pub handshake_result: HandshakeResult,
    // Phase 2: pub chainsync: ..., pub blockfetch: ..., etc.
    mux: RunningMux,
}
```

## Phase 1 Deliverable

### net-cli

A CLI binary that:
1. Takes a `host:port` and network magic as arguments
2. Connects via TCP
3. Runs the handshake protocol (proposes V14/V15)
4. Prints the negotiated version and parameters
5. Disconnects cleanly

Also: a test binary / integration test that runs two nodes (client + server) connected via
`MemBearer`, performing handshake in both directions.

## Dependencies

- `tokio` (rt, net, io-util, time, sync, macros)
- `minicbor` (CBOR encode/decode)
- `bytes` (BytesMut for buffer management)
- `byteorder` (wire format)
- `thiserror` (error types)
- `tracing` (logging)
- `clap` (CLI args, net-cli only)

## Implementation Order

1. `mux/wire.rs` — Segment header encode/decode + tests
2. `bearer/` — Bearer trait + TcpBearer + MemBearer
3. `mux/channel.rs` — ChannelSend/ChannelRecv
4. `mux/scheduler.rs` — Scheduler trait + RoundRobin
5. `mux/egress.rs` + `mux/ingress.rs` — muxer/demuxer tasks
6. `mux/mod.rs` — Mux assembly + RunningMux
7. `codec.rs` — CBOR framing over channels
8. `protocol.rs` — Protocol trait, Agency, driver
9. `protocols/handshake/` — all handshake types, codec, client, server, n2n
10. `lib.rs` — connect/accept API
11. `net-cli/` — CLI binary
12. Integration tests — MemBearer client↔server handshake

## Verification

- **Unit tests**: wire format round-trip, CBOR codec round-trip for each message type,
  state machine transitions, scheduler behavior
- **Integration test**: Two tasks connected via MemBearer, one client one server, complete
  handshake, verify negotiated version
- **Live test**: `net-cli connect relay1.example.com:3001 --magic 764824073` connects to a
  real Cardano mainnet relay and prints the handshake result
- **Server test**: `net-cli serve 0.0.0.0:3001 --magic 764824073` accepts a connection and
  completes handshake (testable against another net-cli instance or a Cardano node)
