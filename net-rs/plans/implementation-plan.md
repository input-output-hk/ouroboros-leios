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
- `ConnectionMode` enum: all three modes implemented (InitiatorOnly, ResponderOnly, Duplex)
- Mux uses `(ProtocolId, u16)` composite keys for channel routing; scheduler stays keyed by
  `ProtocolId` (both directions share priority). `register_with_mode()` for explicit direction.
  Demuxer routes by `(protocol_id, mode)` — accepts segments in both directions.
- Duplex task (`duplex_task.rs`): combines client + server sub-tasks on one mux via
  `connect_duplex()` / `accept_duplex()`. Coordinator spawns duplex tasks when `config.duplex`
  is set. `multi-follow --duplex` flag.
- `ChainStore`: shared in-memory chain state (VecDeque with capacity eviction, watch::channel
  notification). Coordinator populates from `BlockFetched` events (with header from
  `pending_headers` map) and `InjectBlock` commands. Responder tasks read via `Arc<ChainStore>`.
- Server protocol handlers in `net-core::peer::server_handlers` — extracted from serve.rs,
  parameterized on `Arc<ChainStore>` and event senders
- Accept loop: spawned as background task if `listen_address` configured; feeds completed
  connections to coordinator via internal mpsc channel
- `serve` CLI refactored to use coordinator with `InjectBlock`/`InjectRollback` commands
- `multi-follow --listen` enables relay mode (initiator upstream + responder downstream)

**Deferred (Phase 3b: Promotion/Demotion/Churn):**

Can be done before or after Phase 4 — neither blocks Leios protocols. Moderate
scope (1-2 sessions). No new information required from consensus/application.

*Promotion/demotion:*
- `PeerTemperature` enum: Cold (address only), Warm (connected, KeepAlive + PeerSharing),
  Hot (fully active: + ChainSync, BlockFetch, TxSubmission)
- Currently all peers go straight to Hot on connection; need two-phase startup
- Per-peer cancellation tokens (one per protocol group) for dynamic sub-task lifecycle
- New `PeerCommand::Promote(Hot)` / `Demote(Warm)` — peer task spawns/aborts protocol
  sub-tasks accordingly
- Connection setup becomes: connect → handshake → KeepAlive only → promote adds protocols

*Churn (policy layer on top of promotion/demotion):*
- Background timer in coordinator that periodically reshuffles peers
- Configurable target counts: `target_warm_peers`, `target_hot_peers`
- Round-robin reshuffling: demote one hot → warm, promote one warm → hot
- Drop warm → cold (disconnect), connect cold → warm (from PeerSharing discovery)
- Peer quality scoring from existing state (RTT, tip freshness, time connected)
- Cooldown tracking to avoid thrashing

*Already have:* per-peer tip/RTT, PeerSharing discovery, ConnectionMode tracking,
Disconnect command. *Need:* temperature tracking, dynamic sub-task lifecycle,
churn policy config, target peer counts.

**Also deferred:**
- Backoff reset on sustained connection success

**Live-tested:** Duplex against mainnet (backbone.cardano.iog.io:3001, version 15).
Local relay chain: serve → multi-follow --listen → follow. Exponential backoff reconnection.
172 total tests.

### Phase 4: Leios Protocols

Deliverable: LeiosNotify and LeiosFetch protocols integrated into the multi-peer
coordinator, with Praos header/body extensions and priority scheduling.

**Working assumptions:**
- Protocol IDs: LeiosNotify = 18, LeiosFetch = 19 (not yet assigned in CIP)
- Two protocols only; no third protocol for range requests initially
- All Leios data types (EBs, votes, certificates, BLS keys/sigs) are opaque byte blobs,
  same pattern as `WrappedHeader`/`BlockBody`
- BLS crypto verification is out of scope (consensus layer, not networking)

#### Phase 4a: LeiosNotify Protocol — COMPLETE

State machine, Message enum, CBOR codec, client + server async helpers, unit tests.

```
StIdle (Client)  → MsgLeiosNotificationRequestNext → StBusy (Server)
StBusy           → MsgLeiosBlockAnnouncement        → StIdle
StBusy           → MsgLeiosBlockOffer               → StIdle
StBusy           → MsgLeiosBlockTxsOffer            → StIdle
StBusy           → MsgLeiosVotesOffer               → StIdle
StIdle           → MsgDone                          → StDone
```

Files: `net-core/src/protocols/leios_notify/mod.rs`, `codec.rs`

#### Phase 4b: LeiosFetch Protocol — COMPLETE

State machine, Message enum, CBOR codec (including bitmap TX addressing),
client + server async helpers, unit tests. 16 MB max EB size.

```
StIdle       (Client)  → MsgLeiosBlockRequest          → StBlock      (Server)
StBlock      (Server)  → MsgLeiosBlock                 → StIdle

StIdle       (Client)  → MsgLeiosBlockTxsRequest       → StBlockTxs   (Server)
StBlockTxs   (Server)  → MsgLeiosBlockTxs              → StIdle

StIdle       (Client)  → MsgLeiosVotesRequest          → StVotes      (Server)
StVotes      (Server)  → MsgLeiosVoteDelivery          → StIdle

StIdle       (Client)  → MsgLeiosBlockRangeRequest     → StBlockRange (Server)
StBlockRange (Server)  → MsgLeiosNextBlockAndTxsInRange → StBlockRange
StBlockRange (Server)  → MsgLeiosLastBlockAndTxsInRange → StIdle

StIdle       (Client)  → MsgDone                       → StDone
```

Bitmap TX addressing: `MsgLeiosBlockTxsRequest` carries `map<u16, u64>` where each bit
selects one of 64 contiguous transactions at offset `64 × index`.

Files: `net-core/src/protocols/leios_fetch/mod.rs`, `codec.rs`

#### Phase 4c: Parsed Headers + Leios Extensions — COMPLETE

Full Shelley+ header parsing: `WrappedHeader` converted from opaque tuple struct to
named-field struct with `raw: Vec<u8>` and `parsed: Option<HeaderInfo>`. `HeaderInfo`
extracts era, block_number, slot, prev_hash, issuer_vkey, body_size, block_body_hash,
plus CIP-0164 Leios extensions (announced_eb, certified_eb). Array length alone
disambiguates optional fields (10=base, 11=certified_eb, 12=announced_eb, 13=both).
`BlockBody` converted similarly with parsed `LeiosBlockInfo` (extracts EB certificate
from 5th element of Shelley+ block array). Byron headers/blocks return None gracefully.
types.rs split into types/ module (mod.rs, header.rs, block.rs). codec.rs moved to
mux/codec.rs, protocol.rs moved to protocols/protocol.rs. 238 total tests, 17 new
parser tests.

Files: `net-core/src/types/{mod,header,block}.rs`, `net-core/src/mux/codec.rs`,
`net-core/src/protocols/protocol.rs`, `net-core/src/peer/types.rs`, all protocol
codecs and peer modules updated for struct field access and import paths.

#### Phase 4d: Per-Peer Task Integration — COMPLETE

Added LeiosNotify + LeiosFetch to per-peer task trees, plus all supporting types and
plumbing. `leios_enabled: bool` config flag (default false) gates registration.

**Client tasks** (initiator/duplex peers):
- `spawn_leios_notify` — continuous `request_next` loop, translates server notifications
  into `PeerEvent::LeiosBlock{Announced,Offered,TxsOffered}` / `LeiosVotesOffered`
- `spawn_leios_fetch` — command-driven (like `spawn_blockfetch`), receives
  `LeiosFetchCommand::{FetchBlock,FetchVotes}` via internal mpsc channel, reports
  `PeerEvent::LeiosBlockFetched` / `LeiosVotesFetched`

**Server tasks** (responder/duplex peers):
- `serve_leios_notify` — reads from `LeiosStore` notification queue, uses
  `subscribe()` to await new items (same pattern as `serve_chainsync`)
- `serve_leios_fetch` — serves blocks/txs/votes by `(slot, hash)` from `LeiosStore`

**LeiosStore** (`leios_store.rs`): content-addressed blob store, separate from ChainStore
(Leios data keyed by `(slot, hash)`, not part of a linear chain). Methods: `inject_block`,
`inject_block_txs`, `inject_votes`, `get_block`, `get_block_txs`, `get_votes`,
`notifications_after`, `subscribe`. Follows ChainStore's Mutex + watch::channel pattern.

**Types** (`types.rs`): 6 new `PeerEvent` variants (LeiosBlockAnnounced, LeiosBlockOffered,
LeiosBlockTxsOffered, LeiosVotesOffered, LeiosBlockFetched, LeiosVotesFetched), 2 new
`PeerCommand` variants (FetchLeiosBlock, FetchLeiosVotes), 5 new `NetworkEvent` variants,
3 new `NetworkCommand` variants (FetchLeiosBlock, InjectLeiosBlock, InjectLeiosVotes).

**Coordinator** (`coordinator.rs`): stub-forwards all Leios PeerEvents to NetworkEvents.
Creates LeiosStore when `leios_enabled`. Populates LeiosStore from `LeiosBlockFetched`
events and `InjectLeios*` commands. Routes `FetchLeiosBlock` to first connected peer
(smart routing deferred to Phase 4e).

**CLI**: `--leios` flag on `serve` (generates synthetic EBs/votes) and `multi-follow`
(logs Leios notifications). End-to-end tested: `serve --leios → multi-follow --leios`.

247 total tests (9 new: 5 LeiosStore, 2 spawn functions, 2 server handlers).

Files: `net-core/src/peer/{types,mod,leios_store,peer_task,responder_task,duplex_task,server_handlers,coordinator}.rs`,
`net-cli/src/{main,serve,multi_follow}.rs`

#### Phase 4e: Coordinator Extensions

- Smart Leios fetch routing across peers (dedup, pick best peer by RTT)
- Coordinator-level aggregation of Leios announcements
- Integration tests with MemBearer

Files: `net-core/src/peer/coordinator.rs`

#### Phase 4f: Priority Scheduling Verification

- Assign Leios protocol priorities: High = Praos, Medium = LeiosFetch (19),
  Low = LeiosNotify (18) + PeerSharing (10)
- Test that Praos traffic preempts Leios under load

Files: `net-core/src/peer/mod.rs` (protocol ID constants), mux config

#### Deferred

- Freshest-first scheduling (pending upstream discussion)
- Third protocol for range requests (if needed after testing)
- Structured Leios types (replace opaque blobs when spec stabilizes)
- Head-of-line blocking mitigation (dual-LeiosFetch per peer)
- Live Leios testnet testing (when testnet available)

## Workspace Structure

See CLAUDE.md for the up-to-date workspace structure (updated each phase).

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
