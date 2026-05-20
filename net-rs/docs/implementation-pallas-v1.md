# Pallas Network v1 Implementation Notes

Architectural notes from surveying [pallas-network](https://github.com/txpipe/pallas/tree/main/pallas-network)
(v1, `1.0.0-alpha.5`). Focused on Rust API design and patterns.

---

## 1. Crate Overview

```
pallas-network/src/
  lib.rs              -- pub mod facades, miniprotocols, multiplexer
  facades.rs          -- high-level connection types
  multiplexer.rs      -- mux/demux over TCP/Unix/NamedPipe
  miniprotocols/
    mod.rs            -- re-exports all protocols
    common.rs         -- Point, Tip, protocol IDs, network magic constants
    handshake/        -- protocol.rs, codec.rs, client.rs, n2n.rs, n2c.rs
    chainsync/        -- protocol.rs, codec.rs, client.rs, buffer.rs
    blockfetch/       -- protocol.rs, codec.rs, client.rs, server.rs
    txsubmission/     -- protocol.rs, codec.rs, client.rs, server.rs
    keepalive/        -- protocol.rs, codec.rs, client.rs
    peersharing/      -- protocol.rs, codec.rs, client.rs, server.rs
    localstate/       -- client.rs, queries_v16/ (N2C only)
    localtxsubmission/
    txmonitor/
```

**Async runtime**: Tokio (`rt`, `net`, `io-util`, `time`, `sync`, `macros`)

**Key dependencies**: `pallas-codec` (minicbor CBOR), `byteorder`, `socket2` (TCP tuning),
`thiserror`, `tracing`, `itertools`, `rand`

---

## 2. Facade API (User-Facing)

The primary user entry points. Each facade wires up the multiplexer, performs handshake,
and returns protocol client handles.

### PeerClient (N2N)

```rust
let peer = PeerClient::connect("relay:3001", MAINNET_MAGIC).await?;

// Public fields:
peer.chainsync    // chainsync::N2NClient
peer.blockfetch   // blockfetch::Client
peer.txsubmission // txsubmission::Client
peer.peersharing  // peersharing::Client
peer.keepalive    // background task (auto-spawned, 20s interval)
peer.plexer       // RunningPlexer (mux/demux tokio tasks)
```

### PeerServer (N2N)

```rust
let server = PeerServer::accept(&tcp_listener, magic).await?;
// Same fields as PeerClient but subscribed as server role
```

### NodeClient (N2C)

```rust
let mut client = NodeClient::connect("/tmp/node.socket", MAINNET_MAGIC).await?;

// Accessor methods (not public fields):
client.chainsync()    // &mut chainsync::N2CClient
client.statequery()   // &mut localstate::Client
client.submission()   // &mut localtxsubmission::Client
client.monitor()      // &mut txmonitor::Client
```

### Connection Sequence (inside every facade)

1. Create `Bearer` (TCP/Unix/NamedPipe)
2. Create `Plexer`, which splits bearer into read/write halves
3. Subscribe channels for each mini-protocol by protocol ID
4. `plexer.spawn()` → kicks off muxer + demuxer as tokio tasks
5. Perform handshake over protocol 0
6. Construct protocol clients from their channels
7. Spawn keepalive background task (N2N only, 20s interval)

---

## 3. Multiplexer

### Bearer

`Bearer` is a concrete **enum**, not a trait:

```rust
pub enum Bearer {
    Tcp(TcpStream),
    #[cfg(unix)]  Unix(UnixStream),
    #[cfg(windows)] NamedPipe(NamedPipeClient),
}
```

`Bearer::into_split() -> (BearerReadHalf, BearerWriteHalf)` consumes the bearer into
owned halves. Read/write halves are also enums with hand-rolled async methods (no
`dyn AsyncRead`/`dyn AsyncWrite`).

TCP connections get: keepalive 20s interval, `TCP_NODELAY`, linger=0 (via `socket2`).

### Wire Format

8-byte header, big-endian:

| Offset | Size | Field |
|---|---|---|
| 0 | 4 bytes | Timestamp (microseconds since mux start, wraps at ~71 min) |
| 4 | 2 bytes | Protocol ID (bit 15 = direction: 0=initiator, 1=responder) |
| 6 | 2 bytes | Payload length |

Constants: `HEADER_LEN = 8`, `MAX_SEGMENT_PAYLOAD_LENGTH = 65535`

### Architecture

Two independent tokio tasks:

**Demuxer** (read side):
- Owns `BearerReadHalf` + `HashMap<Protocol, mpsc::Sender<Payload>>`
- Reads 8-byte header, then payload bytes
- Looks up protocol ID in hashmap, sends payload to that protocol's channel
- Warns on unregistered protocol IDs

**Muxer** (write side):
- Owns `BearerWriteHalf` + a clock (`Instant`) + single `mpsc::Receiver`
- All protocol agents share clones of the single `mpsc::Sender`
- Reads `(protocol_id, payload)` tuples, writes header + payload + flush

### Channel Subscription

`Plexer` manages protocol registration:

- `subscribe_client(protocol)` — listens on `protocol ^ 0x8000` (server responses),
  sends on raw `protocol` (client requests)
- `subscribe_server(protocol)` — inverse: listens on raw `protocol`, sends on
  `protocol ^ 0x8000`

The `0x8000` XOR convention distinguishes initiator vs responder direction on the wire.

### Scheduling

**No priority or fairness** — the muxer processes messages FIFO from a single shared
`mpsc` channel. All protocol agents contend equally. If one protocol floods the channel,
others are starved.

### Flow Control

Both ingress and egress use bounded `mpsc` channels (buffer = 100). If a protocol agent is
slow to consume, its demuxer channel fills and **blocks the entire bearer read side**,
backpressuring all protocols. There is no per-protocol isolation.

### ChannelBuffer (CBOR Framing)

Wraps an `AgentChannel` and handles the lack of message framing in the mux protocol:

- `send_msg_chunks(msg)` — CBOR-encodes via `minicbor::encode`, chunks at 65KB, sends
  each chunk as a segment
- `recv_full_msg()` — accumulates chunks in a `Vec<u8>`, attempts incremental CBOR decode
  after each chunk, loops until a complete message is decoded
- Uses `minicbor::Decoder::decode()` with `is_end_of_input()` to detect partial messages

---

## 4. Common Types

```rust
pub enum Point {
    Origin,
    Specific(u64, Vec<u8>),  // (slot, block_header_hash)
}

pub struct Tip(pub Point, pub u64);  // (point, block_number)
```

CBOR: `Origin` = `[]` (empty array). `Specific` = `[slot, hash_bytes]`.

### Network Magic Constants

```rust
pub const MAINNET_MAGIC: u64 = 764824073;
pub const TESTNET_MAGIC: u64 = 1097911063;
pub const PREVIEW_MAGIC: u64 = 2;
pub const PRE_PRODUCTION_MAGIC: u64 = 1;
pub const SANCHONET_MAGIC: u64 = 4;
```

### Protocol IDs

| Constant | Value |
|---|---|
| `PROTOCOL_N2N_HANDSHAKE` | 0 |
| `PROTOCOL_N2N_CHAIN_SYNC` | 2 |
| `PROTOCOL_N2N_BLOCK_FETCH` | 3 |
| `PROTOCOL_N2N_TX_SUBMISSION` | 4 |
| `PROTOCOL_N2N_KEEP_ALIVE` | 8 |
| `PROTOCOL_N2N_PEER_SHARING` | 10 |

---

## 5. Mini-Protocol Pattern

Every protocol follows the same structure:

### Module Layout

- `protocol.rs` — `State` enum, `Message` enum, `Error` enum
- `codec.rs` — manual `minicbor::Encode<()>` / `minicbor::Decode<'b, ()>` impls
- `client.rs` — `Client` struct wrapping `(State, ChannelBuffer)`
- `server.rs` — `Server` struct (same pattern), where applicable

### State Machine

Each protocol defines a `State` enum. Agency is checked at runtime:

```rust
impl State {
    fn has_agency(&self) -> bool { ... }  // true when client can send
}

// Before every send:
fn assert_agency_is_ours(&self) -> Result<(), Error> { ... }
// Before every recv:
fn assert_agency_is_theirs(&self) -> Result<(), Error> { ... }
```

State transitions are manual — after send/recv, the code sets `self.0 = State::NewState`.

### CBOR Codec

All messages are CBOR arrays with a leading `u16` tag. Encode/decode are implemented by
hand using `minicbor::Encoder`/`minicbor::Decoder`. The `()` context parameter is unused.

```
Message::Variant(data) => encode as [tag, ...fields]
```

The `Fragment` trait (from `pallas-codec`) bridges CBOR encode/decode to the
`ChannelBuffer`'s `send_msg_chunks`/`recv_full_msg`.

### Client API Pattern

Each client provides two levels:

1. **Low-level**: separate `send_*()` and `recv_*()` methods for each message
2. **High-level**: combined methods that send + recv in one call

```rust
// Low-level
client.send_request_next().await?;
let resp = client.recv_while_can_await().await?;

// High-level
let resp = client.request_next().await?;
```

### Error Handling

Each protocol defines its own error enum via `thiserror::Error`:

```rust
pub enum ClientError {
    AgencyIsOurs,
    AgencyIsTheirs,
    InvalidInbound,
    InvalidOutbound,
    IntersectionNotFound,  // protocol-specific
    Plexer(multiplexer::Error),
}
```

---

## 6. Handshake

### Types

```rust
pub struct VersionTable<T: Debug + Clone> {
    pub values: HashMap<u64, T>,
}

pub enum Message<D: Debug + Clone> {
    Propose(VersionTable<D>),
    Accept(VersionNumber, D),
    Refuse(RefuseReason),
    QueryReply(VersionTable<D>),
}
```

### N2N Version Data

```rust
pub struct VersionData {
    pub network_magic: u64,
    pub initiator_only_diffusion_mode: bool,
    pub peer_sharing: Option<u8>,   // None for v7-v10
    pub query: Option<bool>,        // None for v7-v10
}
```

Encodes as 2-element CBOR array (v7-v10) or 4-element (v11+). Supports V7 through V14
via `VersionTable::v7_and_above(magic)`.

### Client API

```rust
pub type N2NClient = Client<n2n::VersionData>;

pub enum Confirmation<D> {
    Accepted(VersionNumber, D),
    Rejected(RefuseReason),
    QueryReply(VersionTable<D>),
}

// One-shot API:
let result = client.handshake(versions).await?;
```

After handshake, `client.unwrap()` recovers the `AgentChannel` for reuse.

### CBOR

| Tag | Message |
|---|---|
| 0 | `[0, version_table_map]` — Propose / ReplyVersions |
| 1 | `[1, version_number, version_data]` — Accept |
| 2 | `[2, refuse_reason]` — Refuse |
| 3 | `[3, version_table_map]` — QueryReply |

Version table is a definite-length CBOR map with keys sorted ascending.

---

## 7. ChainSync

### Generic Over Content Type

```rust
pub enum Message<C> {
    RequestNext,
    AwaitReply,
    RollForward(C, Tip),
    RollBackward(Point, Tip),
    FindIntersect(Vec<Point>),
    IntersectFound(Point, Tip),
    IntersectNotFound(Tip),
    Done,
}

pub type N2NClient = Client<HeaderContent>;   // headers only
pub type N2CClient = Client<BlockContent>;    // full blocks
```

### Content Types

```rust
pub struct HeaderContent {
    pub variant: u8,                    // era tag (0=Byron, 2=Shelley, ...)
    pub byron_prefix: Option<(u8, u64)>, // extra tuple for Byron headers
    pub cbor: Vec<u8>,                  // raw CBOR bytes
}

pub struct BlockContent(pub Vec<u8>);   // raw CBOR bytes, Deref<Target=[u8]>
pub struct SkippedContent;              // decodes by calling d.skip()
```

Byron headers decode as `[variant, [[a, b], #6.24(bytes)]]`. Shelley+ headers are
`[variant, #6.24(bytes)]`. Both use CBOR tag 24 for embedded CBOR.

### Client API

```rust
client.find_intersect(points).await?           // -> (Option<Point>, Tip)
client.request_next().await?                   // -> NextResponse<O>
client.request_or_await_next().await?          // handles MustReply state
client.intersect_origin().await?               // -> Point
client.intersect_tip().await?                  // -> Point
client.send_done().await?
```

`NextResponse<C>` is:
```rust
pub enum NextResponse<C> {
    RollForward(C, Tip),
    RollBackward(Point, Tip),
    Await,
}
```

### RollbackBuffer Utility

`VecDeque<Point>` that tracks chain points in memory:
- `roll_forward(point)` — append
- `roll_back(point)` — truncate to intersection or clear if out of scope
- `pop_with_depth(min_depth)` — drain confirmed points above a minimum depth

---

## 8. BlockFetch

### Types

```rust
pub enum Message {
    RequestRange { range: (Point, Point) },
    ClientDone,
    StartBatch,
    NoBlocks,
    Block { body: Vec<u8> },
    BatchDone,
}
```

Block body is wrapped in CBOR tag 24 (embedded CBOR) + raw bytes.

### Client API

```rust
let has_blocks = client.request_range(from, to).await?;  // -> bool (StartBatch vs NoBlocks)
let block = client.recv_while_streaming().await?;          // -> Option<Vec<u8>>
client.fetch_single(point).await?                          // -> Vec<u8>
client.fetch_range(from, to).await?                        // -> Vec<Vec<u8>>
client.send_done().await?
```

### Server API

```rust
let request = server.recv_while_idle().await?;   // -> Option<BlockRequest>
server.send_block_range(bodies).await?;           // handles StartBatch/Block.../BatchDone
```

---

## 9. TxSubmission

### Types

```rust
pub struct EraTxId(pub u16, pub Vec<u8>);           // era-tagged tx id
pub struct EraTxBody(pub u16, pub Vec<u8>);          // era-tagged tx body
pub struct TxIdAndSize<TxId>(pub TxId, pub TxSizeInBytes);

pub enum Message<TxId, TxBody> {
    Init,
    RequestTxIds(Blocking, TxCount, TxCount),  // blocking, ack, req
    ReplyTxIds(Vec<TxIdAndSize<TxId>>),
    RequestTxs(Vec<TxId>),
    ReplyTxs(Vec<TxBody>),
    Done,
}
```

### Agency Inversion

The "client" (tx submitter) has agency in all states except `Idle`. The server drives
the protocol by sending `RequestTxIds`/`RequestTxs`. This is the pull-based design.

### Client API

```rust
pub type Client = GenericClient<EraTxId, EraTxBody>;

client.send_init().await?;
let request = client.next_request().await?;  // -> Request<TxId>
match request {
    Request::TxIds(ack, req) => client.reply_tx_ids(ids).await?,
    Request::TxIdsNonBlocking(ack, req) => client.reply_tx_ids(ids).await?,
    Request::Txs(ids) => client.reply_txs(bodies).await?,
}
client.send_done().await?;
```

### CBOR Detail

`EraTxBody` encodes as `[era, #6.24(bytes)]` (CBOR-in-CBOR). `EraTxId` is `[era, bytes]`.
Inner lists use **indefinite-length** CBOR arrays.

---

## 10. KeepAlive

### Cookie in State

```rust
pub enum State {
    Client,
    Server(Cookie),  // stores expected cookie for validation
    Done,
}
```

The state itself carries the expected cookie, so response validation is a state check.

### Client API

```rust
client.send_keepalive_request().await?;   // generates random u16 cookie
client.recv_keepalive_response().await?;  // validates cookie match
client.keepalive_roundtrip().await?;      // convenience: send + recv
```

Cookie is generated via `rand::thread_rng().gen::<u16>()`.

---

## 11. PeerSharing

### Types

```rust
pub type Amount = u8;

pub enum PeerAddress {
    V4(Ipv4Addr, Port),
    V6(Ipv6Addr, Port),
}

pub enum State {
    Idle,
    Busy(Amount),  // stores requested amount for validation
    Done,
}
```

### CBOR

IPv4: `[0, u32, port]`. IPv6: `[1, w1, w2, w3, w4, port]` (128-bit address split into
four `u32` words). Peer lists use indefinite-length CBOR arrays.

### Client API

```rust
client.send_share_request(amount).await?;
let peers = client.recv_peer_addresses().await?;
client.send_done().await?;
```

Size limit: 5,760 bytes (4 TCP segments of 1,440 bytes).

---

## 12. Design Assessment

### Strengths

- **Simple, imperative API** — `connect()`, get clients, call methods. Easy to use for
  scripts and tools.
- **Clean module structure** — each protocol is self-contained with consistent layout.
- **Generic ChainSync** — `Message<C>` + type aliases cleanly support N2N (headers) and
  N2C (blocks) variants.
- **Concrete bearer enum** — no vtable overhead, exhaustive match ensures all transports
  handled.

### Weaknesses / Gaps for net-rs

- **No mux-level fairness** — single FIFO channel, no priority or round-robin. Leios's
  large messages would head-of-line block Praos.
- **No per-protocol backpressure isolation** — slow consumer blocks entire bearer read.
- **Runtime agency checks** — state machine transitions are imperative, not
  compile-time enforced. Invalid transitions are caught as runtime errors.
- **No SDU size limiting** — segments can be up to 65KB. The Cardano node uses 12KB SDUs.
  Pallas uses the full 65KB, which means interleaving granularity is coarse.
- **Bearer is not extensible** — adding a new transport requires modifying the enum. A
  trait-based approach would be more open.
- **No timeout enforcement** — protocol-level timeouts from the spec are not implemented.
- **No connection manager** — each facade is a single connection. No peer lifecycle,
  no promotion/demotion, no multiplexed peer management.
- **Version negotiation is client-only** — the server side of handshake exists but is
  minimal; the `acceptable` symmetry from the Haskell implementation is not present.

### Key Differences from Haskell

| Aspect | Haskell | Pallas v1 |
|---|---|---|
| Agency enforcement | Compile-time (type system) | Runtime checks |
| Mux scheduling | Round-robin with re-queue | Single FIFO channel |
| Mux SDU size | 12,288 bytes | 65,535 bytes |
| Ingress overflow | Fatal connection kill | mpsc backpressure (blocks all) |
| Egress backpressure | Soft limit (256KB/Wanton) | mpsc bounded(100) |
| CBOR framing | Incremental `DecodeStep` coroutine | Accumulate + retry decode |
| Pipelining | First-class (`YieldPipelined`) | Not supported |
| Connection manager | Full state machine with promotion | None (single connection) |
| Codec structure | Parametric (injected encoders) | Manual per-protocol impls |

### What to Take from Pallas for net-rs

- The `ChannelBuffer` accumulate-and-retry-decode approach works and is simple
- `Point`/`Tip` types and CBOR encoding are battle-tested
- The facade pattern (connect → handshake → return protocol handles) is good UX
- Era-tagged content types (`HeaderContent`, `EraTxId`, `EraTxBody`) are practical
- Manual CBOR codecs with `minicbor` are straightforward

### What to Improve in net-rs

- Mux needs priority/WFQ scheduling (per masterplan)
- SDU size should be configurable, default 12KB for Cardano compatibility
- Per-protocol ingress buffers with configurable limits (not shared backpressure)
- Protocol timeouts from the spec must be enforced
- Trait-based bearer for extensibility
- Consider compile-time agency enforcement (Rust typestate pattern)
- Pipelining support for BlockFetch
