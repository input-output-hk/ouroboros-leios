# Pallas Network v2 Implementation Notes

Architectural notes from surveying [pallas-network2](https://github.com/txpipe/pallas/tree/main/pallas-network2)
(`1.0.0-alpha.2`, unpublished). This is a complete rewrite of v1 with an event-driven,
multi-peer architecture.

---

## 1. Crate Overview

```
pallas-network2/src/
  lib.rs              -- Core traits (Message, Interface, Behavior), Manager, OutboundQueue
  bearer.rs           -- TCP/Unix/NamedPipe transport + wire format
  interface.rs        -- TcpInterface, TcpListenerInterface (connection pools)
  protocol/
    mod.rs            -- Error enum, re-exports
    common.rs         -- Point, network magic, protocol channel IDs
    handshake/        -- mod.rs, n2n.rs, n2c.rs
    chainsync.rs
    blockfetch.rs
    txsubmission.rs
    keepalive.rs
    peersharing.rs
  behavior/
    mod.rs            -- AnyMessage, ConnectionState, re-exports
    initiator/
      mod.rs          -- InitiatorBehavior, InitiatorState, PeerVisitor trait
      connection.rs, handshake.rs, keepalive.rs, chainsync.rs,
      blockfetch.rs, discovery.rs, promotion.rs
    responder/
      mod.rs + per-protocol files (mirror of initiator)
  emulation/
    mod.rs            -- Emulator<M,R>, Rules trait, ReplyQueue
    happy.rs          -- "Happy path" emulation rules
    initiator_mock.rs -- Mock initiator for testing
```

**Rust edition**: 2024

**Async runtime**: Tokio (behind feature flags) + `futures` for Stream/FusedStream

**Key deps**: `pallas-codec` (minicbor), `byteorder`, `socket2`, `futures`,
`trait-variant`, `thiserror`, `tracing`, `opentelemetry`

**Feature flags**: `emulation` (default, enables tokio+rand), `blueprint`

---

## 2. Three-Layer Architecture

```
    User
     |  Commands ↓   Events ↑
     v
  Manager  ─── select! polls both ───
     |                                |
     v                                v
  Behavior                       Interface
  (business logic)               (IO transport)
     |                                |
     |  InterfaceCommands ↓           |  InterfaceEvents ↑
     +────────────────────────────────+
```

**Manager** reconciles two `FusedStream`s:
- Behavior yields `BehaviorOutput::InterfaceCommand(cmd)` → routed to `interface.dispatch(cmd)`
- Behavior yields `BehaviorOutput::ExternalEvent(evt)` → returned to user
- Interface yields `InterfaceEvent` → passed to `behavior.handle_io(evt)`

The user drives the system with `poll_next()` (returns external events) and
`execute(cmd)` (sends commands to behavior).

---

## 3. Core Traits

### Message

The central wire protocol abstraction:

```rust
pub trait Message: Send + 'static + Debug + Sized + Clone {
    fn channel(&self) -> Channel;                                    // u16 protocol ID
    fn payload(&self) -> Payload;                                    // serialize to Vec<u8>
    fn from_payload(channel: Channel, payload: &mut Payload) -> Option<Self>;  // incremental decode
    fn into_payload(self) -> (Channel, Payload);
    fn into_chunks(self) -> (Channel, Vec<Payload>);                 // splits at 65535 bytes
}
```

The concrete implementation is `AnyMessage` — an enum wrapping all six protocol message types.
`from_payload()` dispatches by channel ID to the correct CBOR decoder.

### Interface

```rust
pub trait Interface<M: Message>:
    Unpin + FusedStream + Stream<Item = InterfaceEvent<M>>
{
    fn dispatch(&mut self, cmd: InterfaceCommand<M>);
}
```

Commands: `Connect(PeerId)`, `Send(PeerId, M)`, `Disconnect(PeerId)`

Events: `Connected`, `Disconnected`, `Sent`, `Recv(PeerId, Vec<M>)`, `Error`, `Idle`

### Behavior

```rust
pub trait Behavior:
    Sized + Unpin + FusedStream + Stream<Item = BehaviorOutput<Self>> + Send + 'static
{
    type Event: Debug + Send + 'static;
    type Command;
    type PeerState: Default;
    type Message: Message + Debug + Send + 'static;

    fn handle_io(&mut self, event: InterfaceEvent<Self::Message>);
    fn execute(&mut self, cmd: Self::Command);
}
```

### Manager

```rust
pub struct Manager<I, B, M> {
    interface: I,
    behavior: B,
}

impl Manager {
    pub fn new(interface: I, behavior: B) -> Self;
    pub async fn poll_next(&mut self) -> Option<B::Event>;  // drives everything
    pub fn execute(&mut self, cmd: B::Command);
}
```

### PeerId

```rust
pub struct PeerId { pub host: String, pub port: u16 }
```

Implements `FromStr` (parses `"host:port"`), `Display`, `Hash`, `Eq`.

---

## 4. Bearer / Transport

### Bearer Enum

Same as v1 — concrete enum, not a trait:

```rust
pub enum Bearer {
    Tcp(TcpStream),
    #[cfg(unix)]  Unix(UnixStream),
    #[cfg(windows)] NamedPipe(NamedPipeClient),
}
```

`into_split() -> (BearerReadHalf, BearerWriteHalf)`. TCP: keepalive 20s, nodelay, linger=0.

### Wire Format

Standard Ouroboros 8-byte header (identical to v1):

| Offset | Size | Field |
|---|---|---|
| 0 | 4 bytes | Timestamp (u32 big-endian, microseconds since start) |
| 4 | 2 bytes | Protocol/channel ID (bit 15 = direction) |
| 6 | 2 bytes | Payload length |

### Key Difference from v1: No Mux/Demux Layer

v1 had `Muxer`, `Demuxer`, `Plexer`, `AgentChannel`, `ChannelBuffer` as separate
abstractions with background tokio tasks routing segments between mini-protocols via
mpsc channels.

v2 **eliminates all of that**. The bearer read/write halves handle segmentation directly:

- `BearerReadHalf::read_full_msgs<M>(partial_chunks)` — reads segments, reassembles
  partial messages using a `HashMap<Channel, Payload>` buffer, returns complete messages
- `BearerWriteHalf::write_message<M>(msg, timestamp, mode)` — calls `msg.into_chunks()`,
  writes each chunk with the direction mode bit

The shared writer is `Arc<Mutex<BearerWriteHalf>>` — multiple concurrent sends to the
same peer are serialized through the mutex.

---

## 5. Interface Layer

### TcpInterface (outbound/initiator)

Uses `TcpConnectionPool` with mode = `PROTOCOL_CLIENT` (0x0000).

- `dispatch(Connect)` → spawns async TCP connect future
- `dispatch(Send)` → enqueues write future using `SharedWriter`
- `dispatch(Disconnect)` → spawns shutdown future
- Implements `Stream<Item = InterfaceEvent<M>>` via `FuturesUnordered`
- On connect: splits bearer, stores writer in `HashMap<PeerId, SharedWriter>`, spawns
  continuous recv future
- On recv: decodes messages, re-arms recv future for next read

### TcpListenerInterface (inbound/responder)

Uses `TcpConnectionPool` with mode = `PROTOCOL_SERVER` (0x8000).

- Wraps a `TcpListener` with a standing accept future
- `poll_next()` first polls accept, then polls the connection pool
- Ignores `Connect` commands (logs warning)
- On accept: creates `PeerId` from remote address, emits `Connected` event

### Connection Pool (shared internal)

```rust
struct TcpConnectionPool<M> {
    writers: HashMap<PeerId, SharedWriter>,  // Arc<Mutex<BearerWriteHalf>>
    futures: FuturesUnordered<InterfaceFuture<M>>,
    clock: Instant,
    mode: u16,  // PROTOCOL_CLIENT or PROTOCOL_SERVER
}
```

No background tasks — everything is poll-driven via `FuturesUnordered`.

---

## 6. Protocol Layer

Each protocol defines types and a **pure state machine** with no I/O:

- `State` enum with `fn apply(&self, msg) -> Result<State, Error>` for transitions
- `Message` enum with manual `minicbor::Encode`/`Decode` impls
- Protocol-specific types

### Error Type

```rust
pub enum Error {
    AgencyIsOurs,
    AgencyIsTheirs,
    InvalidInbound,
    InvalidOutbound,
    Other(String),
}
```

### Handshake

States: `Propose` → `Confirm(VersionTable<D>)` → `Done(DoneState<D>)`

`DoneState<D>`: `Accepted(VersionNumber, D)`, `Rejected(RefuseReason)`, `QueryReply(VersionTable<D>)`

The `Confirm` state carries the proposed version table so the behavior layer can inspect
it. The `Done` state carries the result for the behavior to consume.

N2N VersionData: same as v1 (`network_magic`, `initiator_only_diffusion_mode`,
`peer_sharing`, `query`). Factory methods: `v7_and_above()`, `v7_to_v10()`, `v11_and_above()`.

### ChainSync

Channel ID: 2. Generic over content type `C`.

States: `Idle(Data<C>)`, `CanAwait`, `MustReply`, `Intersect(Vec<Point>)`, `Done`

**`Data<C>`** — accumulator for consumed state:
```rust
pub enum Data<C> {
    New,
    Intersection(Point, Tip),
    NoIntersection(Tip),
    Content(C, Tip),        // RollForward result
    Rollback(Point, Tip),   // RollBackward result
    Drained,
}
```

`State::drain() -> Option<Data<C>>` extracts accumulated data and resets to `Drained`.
This enables pull-based consumption by the behavior layer.

Content types: `HeaderContent`, `BlockContent`, `SkippedContent` (same as v1).

### BlockFetch

Channel ID: 3

States: `Idle`, `Busy(Range)`, `Streaming(Option<Body>)`, `Done`

The `Busy` state carries the requested range. `Streaming` carries the last received block
body (consumed via drain pattern).

### TxSubmission

Channel ID: 4

States: `Init`, `Idle`, `TxIdsNonBlocking`, `TxIdsBlocking`, `Txs(Vec<EraTxBody>)`, `Done`

The `Txs` state carries received transaction bodies for consumption.

Types: `EraTxId(u16, Vec<u8>)`, `EraTxBody(u16, Vec<u8>)`, `TxIdAndSize<TxID>` — same as v1.

### KeepAlive

Channel ID: 8

States: `Client(ClientState)`, `Server(Cookie)`, `Done`

`ClientState`: `Empty`, `Response(Cookie)` — stores received cookie for consumption.

### PeerSharing

Channel ID: 10

States: `Idle(IdleState)`, `Busy(Amount)`, `Done`

`IdleState`: `Empty`, `Response(Vec<PeerAddress>)` — stores received peer list.

---

## 7. Behavior Layer

### AnyMessage

The concrete `Message` implementation multiplexing all protocols:

```rust
pub enum AnyMessage {
    Handshake(handshake::Message<n2n::VersionData>),
    KeepAlive(keepalive::Message),
    ChainSync(chainsync::Message<HeaderContent>),
    PeerSharing(peersharing::Message),
    BlockFetch(blockfetch::Message),
    TxSubmission(txsubmission::Message),
}
```

`from_payload()` dispatches by channel ID to the correct CBOR decoder.

### Per-Peer State

```rust
pub struct InitiatorState {
    pub connection: ConnectionState,    // New/Connecting/Connected/Initialized/Disconnected/Errored
    pub promotion: PromotionTag,        // Cold/Warm/Hot/Banned
    pub handshake: handshake::State<n2n::VersionData>,
    pub keepalive: keepalive::State,
    pub peersharing: peersharing::State,
    pub blockfetch: blockfetch::State,
    pub chainsync: chainsync::State<HeaderContent>,
    pub tx_submission: txsubmission::State,
    pub violation: bool,
    pub error_count: u32,
    pub continue_sync: bool,
}
```

`apply_msg(&mut self, msg)` advances each protocol's state machine based on `msg.channel()`.
Sets `violation = true` on invalid transitions.

### PeerVisitor Trait

Each sub-behavior implements this to react to peer lifecycle events:

```rust
pub trait PeerVisitor {
    fn visit_connected(&mut self, pid, state, outbound) {}
    fn visit_disconnected(&mut self, pid, state, outbound) {}
    fn visit_errored(&mut self, pid, state, outbound) {}
    fn visit_discovered(&mut self, pid, state, outbound) {}
    fn visit_inbound_msg(&mut self, pid, msg, state, outbound) {}
    fn visit_outbound_msg(&mut self, pid, msg, state, outbound) {}
    fn visit_tagged(&mut self, pid, state, outbound) {}
    fn visit_housekeeping(&mut self, peers, outbound) {}
}
```

The `all_visitors!` macro fans out each event to all registered sub-behaviors:
`promotion`, `connection`, `handshake`, `keepalive`, `discovery`, `chainsync`, `blockfetch`.

### Initiator

**Sub-behaviors**:

| Sub-behavior | What it does |
|---|---|
| `PromotionBehavior` | Cold→Warm→Hot ladder with configurable limits, banning |
| `ConnectionBehavior` | Auto connect/disconnect based on promotion tag |
| `HandshakeBehavior` | Auto-proposes handshake on connect, emits `PeerInitialized` |
| `KeepaliveBehavior` | Sends keepalive during housekeeping |
| `DiscoveryBehavior` | Requests peers via PeerSharing, feeds into promotion |
| `ChainSyncBehavior` | Intersection finding + header streaming |
| `BlockFetchBehavior` | Block request queue, dispatches to available peers |

**Commands**:
```rust
pub enum InitiatorCommand {
    IncludePeer(PeerId),
    Housekeeping,
    StartSync(Vec<Point>),
    ContinueSync(PeerId),
    RequestBlocks(BlockRange),
    SendTx(PeerId, EraTxId, EraTxBody),
    BanPeer(PeerId),
    DemotePeer(PeerId),
}
```

**Events**:
```rust
pub enum InitiatorEvent {
    PeerInitialized(PeerId, AcceptedVersion),
    IntersectionFound(PeerId, Point, Tip),
    BlockHeaderReceived(PeerId, HeaderContent, Tip),
    RollbackReceived(PeerId, Point, Tip),
    BlockBodyReceived(PeerId, Body),
    TxRequested(PeerId, EraTxId),
}
```

### Responder

Mirrors the initiator with server-side commands/events:

**Commands**: `ProvideIntersection`, `ProvideHeader`, `ProvideBlocks`, `ProvidePeers`,
`BanPeer`, `DisconnectPeer`

**Events**: `PeerInitialized`, `PeerDisconnected`, `IntersectionRequested`,
`NextHeaderRequested`, `BlockRangeRequested`, `PeersRequested`, `TxReceived`

### Promotion System

```rust
pub struct PromotionConfig {
    pub max_peers: usize,       // 100
    pub max_warm_peers: usize,  // 50
    pub max_hot_peers: usize,   // 10
    pub max_error_count: u32,   // 1
}
```

Maintains `cold_peers`, `warm_peers`, `hot_peers`, `banned_peers` as `HashSet<PeerId>`.
Auto-promotes when deficits exist. Bans on violation or excess errors.
Emits OpenTelemetry gauges for each tier.

---

## 8. Emulation Layer

Feature-gated (`emulation`, on by default).

```rust
pub trait Rules {
    type Message: Message + Clone + 'static;
    fn reply_to(&self, pid: PeerId, msg: Self::Message, jitter: Duration, queue: &mut ReplyQueue<Self::Message>);
    fn should_connect(&self, pid: PeerId) -> bool { true }
    fn jitter(&self) -> Duration { /* random 0..3s */ }
}

pub struct Emulator<M, R: Rules<Message = M>> { ... }
```

`Emulator` implements `Interface<M>` — dispatches commands by scheduling jittered futures
(connect → Connected, send → Sent + rules.reply_to, disconnect → Disconnected). No real
I/O. Useful for testing behavior logic in isolation.

---

## 9. Usage Examples

### Initiator (client connecting to peers)

```rust
let interface = TcpInterface::new();
let behavior = InitiatorBehavior::default();
let mut network = Manager::new(interface, behavior);

network.execute(InitiatorCommand::IncludePeer("relay:3001".parse()?));
network.execute(InitiatorCommand::StartSync(vec![Point::Origin]));

loop {
    if let Some(event) = network.poll_next().await {
        match event {
            InitiatorEvent::BlockHeaderReceived(pid, header, tip) => { ... }
            InitiatorEvent::RollbackReceived(pid, point, tip) => { ... }
            InitiatorEvent::BlockBodyReceived(pid, body) => { ... }
            _ => {}
        }
    }
    // Periodically:
    network.execute(InitiatorCommand::Housekeeping);
}
```

### Responder (server accepting connections)

```rust
let listener = TcpListener::bind("0.0.0.0:3001").await?;
let interface = TcpListenerInterface::new(listener);
let behavior = ResponderBehavior::default();
let mut network = Manager::new(interface, behavior);

loop {
    if let Some(event) = network.poll_next().await {
        match event {
            ResponderEvent::IntersectionRequested(pid, points) => {
                network.execute(ResponderCommand::ProvideIntersection(pid, point, tip));
            }
            ResponderEvent::NextHeaderRequested(pid) => {
                network.execute(ResponderCommand::ProvideHeader(pid, header, tip));
            }
            ResponderEvent::BlockRangeRequested(pid, range) => {
                network.execute(ResponderCommand::ProvideBlocks(pid, blocks));
            }
            _ => {}
        }
    }
}
```

---

## 10. Design Assessment

### Strengths

- **Clean separation** — IO (Interface), logic (Behavior), orchestration (Manager) are
  fully decoupled. Easy to test each in isolation.
- **Multi-peer** — manages many peers with per-peer state, promotion ladder, and
  auto-connect/disconnect. v1 was single-connection only.
- **Emulation** — `Emulator` + `Rules` trait enables testing without real sockets.
- **Pure state machines** — protocol states have `apply(msg) -> Result<State>` with no I/O
  mixed in. Behavior layer drives transitions.
- **Visitor pattern** — sub-behaviors compose cleanly via `PeerVisitor` trait + macro
  fanout.
- **OpenTelemetry** — built-in metrics for connection and promotion tracking.
- **Responder support** — first-class server-side behavior, not just client.

### Weaknesses / Gaps for net-rs

- **No mux fairness** — `Arc<Mutex<BearerWriteHalf>>` serializes all writes. No priority
  or round-robin between protocols. Same problem as v1 but with mutex contention instead
  of channel contention.
- **65KB SDU size** — still uses `MAX_SEGMENT_PAYLOAD_LENGTH = 65535` instead of the
  Cardano standard 12,288. Coarse interleaving granularity.
- **No per-protocol backpressure** — all protocols share the same write mutex and read
  future. A slow protocol can block others.
- **No timeout enforcement** — protocol-level timeouts from the spec are not implemented.
- **Incomplete** — `1.0.0-alpha.2`, some commands (SendTx) noted as not yet implemented.
  Responder behavior is less fleshed out than initiator.
- **Bearer still an enum** — same extensibility limitation as v1.
- **No pipelining** — no support for BlockFetch pipelining or ChainSync pipelining.
- **`poll_next()` returns `None` for internal routing** — user must handle `None` and
  re-poll, which is slightly awkward.

### Key Differences from v1

| Aspect | v1 | v2 |
|---|---|---|
| Architecture | Single-connection imperative | Multi-peer event-driven |
| Mux/Demux | Separate tokio tasks + mpsc | Eliminated; bearer reads/writes directly |
| Protocol state | Mixed with I/O in Client structs | Pure `apply(msg) -> State` |
| Multi-peer | Not supported | Built-in with promotion ladder |
| Composition | Monolithic facade | Visitor pattern + sub-behaviors |
| Testing | No mock support | `Emulator` + `Rules` trait |
| Server support | Minimal | Full `ResponderBehavior` |
| Metrics | None | OpenTelemetry gauges |
| Rust edition | 2021 | 2024 |

### Key Differences from Haskell

| Aspect | Haskell | Pallas v2 |
|---|---|---|
| Agency enforcement | Compile-time (type system) | Runtime `apply()` checks |
| Mux scheduling | Round-robin with Wanton re-queue | Mutex-serialized writes |
| Mux SDU size | 12,288 bytes | 65,535 bytes |
| Ingress overflow | Fatal connection kill | No limit enforcement |
| Pipelining | First-class (YieldPipelined) | Not supported |
| Connection manager | Full state machine with duplex | Promotion ladder (simpler) |
| Codec | Incremental DecodeStep coroutine | Accumulate + retry in `from_payload` |
| Behavior composition | STM-based concurrent actors | Visitor pattern + select! loop |

### What to Take from v2 for net-rs

- The **Interface/Behavior/Manager** layering is clean and worth adopting
- **Pure state machines** with `apply(msg) -> Result<State>` are a good pattern
- The **`AnyMessage` enum** dispatching by channel ID is practical for multi-protocol mux
- **Promotion system** (Cold/Warm/Hot) for peer lifecycle management
- **Emulator** for testing without real sockets
- The **visitor pattern** for composing per-protocol behavior is elegant

### What to Improve in net-rs

- Restore a proper mux layer with per-protocol egress queues and priority/WFQ scheduling
- Use 12KB SDUs for Cardano wire compatibility
- Per-protocol ingress buffers with configurable limits
- Enforce protocol timeouts from the spec
- Consider trait-based bearer for extensibility
- Add pipelining support (at least for BlockFetch)
- Consider typestate pattern for compile-time agency enforcement
