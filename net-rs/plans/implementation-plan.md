# net-rs Phase 1 Implementation Plan

## Context

net-rs is a greenfield Rust implementation of the Cardano mini-protocol network stack for
Praos and Leios. This plan covers the initial crate setup and Phase 1 (multiplexer +
handshake + CLI test connecting to an existing node), with structural decisions informed by
Leios requirements so we don't need to refactor later.

Key references (all in `docs/`): `praos-network.md` (protocol spec), `leios-changes.md`
(what Leios needs from the mux), `implementation-haskell.md` and
`implementation-pallas-v1.md` / `v2.md` (prior art).

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

## Phase 1 Deliverable: net-cli

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
