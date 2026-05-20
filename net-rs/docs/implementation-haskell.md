# Haskell Implementation Notes

Architectural notes from surveying the [ouroboros-network](https://github.com/IntersectMBO/ouroboros-network)
Haskell codebase. Focused on functional design, not Haskell-specific details.

---

## 1. Layer Stack

```
                  Peer Selection Governor
                         |
              Diffusion Layer (run/runM)
                    /          \
           Connection          Server
            Manager         (accept loop)
                \              /
              Connection Handler
                    |
               Mux (network-mux)
                    |
               Bearer (TCP socket)
```

**Diffusion** is the top-level orchestrator. It spawns concurrently:
- **Peer Selection Governor** — decides peer targets, drives connect/disconnect
- **Churn Governor** — adjusts peer targets over time
- **Server** (if responder mode) — accept loop for inbound connections
- **Inbound Governor** — tracks inbound peer states

All threads race; first failure propagates.

---

## 2. Multiplexer (`network-mux`)

### Initialization

`Mux::new` takes a list of `MiniProtocolInfo` descriptors and creates:
- A map of `(MiniProtocolNum, MiniProtocolDir) -> MiniProtocolState` for all registered protocols
- A command queue for control (start protocol, shutdown)
- A status variable (Ready / Failed / Stopping / Stopped)

### Runtime Architecture

`Mux::run` spawns three concurrent components:

1. **Muxer (egress)** — reads from a shared bounded queue (capacity 100), segments data
   into SDUs, writes to the bearer
2. **Demuxer (ingress)** — reads SDUs from the bearer, dispatches payloads into
   per-protocol ingress queues
3. **Monitor loop** — handles job completions, control commands, and on-demand protocol
   activation when data arrives

### Egress: Wanton + EgressQueue

Each mini-protocol has a "Wanton" — an accumulation buffer for outgoing data. When a
protocol writes bytes:
- If the Wanton was empty, it's enqueued onto the shared `EgressQueue`
- If already enqueued (has data), bytes are just appended — no duplicate queue entry

The muxer thread pulls one Wanton at a time:
1. Extract at most `sduSize` bytes
2. If data remains, **re-enqueue the Wanton at the back** — this is the fairness mechanism
3. After processing one, greedily batch up to 100 more SDUs for vectored I/O
4. When the queue empties, pace with a delay to avoid busy-spinning

**Soft backpressure**: `send` blocks if the Wanton accumulates > 256KB.

### Ingress: Per-Protocol Queues

Each mini-protocol has an ingress queue with a configurable byte limit. The demuxer:
1. Reads an SDU from the bearer
2. Reverses the direction bit (incoming Responder → local Initiator)
3. Looks up the target protocol by `(num, dir)`
4. Checks `current_length + new_sdu_length <= limit`
5. If exceeded: **fatal error** — tears down the connection (no graceful backpressure)
6. Otherwise appends to the queue

### Protocol Start Modes

- **StartEagerly** — launches immediately (initiator-side protocols)
- **StartOnDemand** — waits for first incoming data (responder-side)
- **StartOnDemandAny** — starts on any data arrival

### Shutdown

Enqueues shutdown command. Cancels all protocol jobs. Waits up to **2 seconds** for egress
queue to drain. Then closes.

### Constants

| Constant | Value |
|---|---|
| Header size | 8 bytes |
| Protocol ID bits | 15 (bit 15 = direction) |
| Egress queue capacity | 100 entries |
| Egress soft buffer limit | 262,143 bytes (~256KB) |
| Max SDUs per batch | 100 |
| Socket SDU payload size | 12,288 bytes (12KB) |
| Socket batch size | 131,072 bytes (128KB) |
| Read buffer size | 131,072 bytes (128KB) |
| Shutdown drain timeout | 2 seconds |

---

## 3. Typed-Protocol Framework

### Protocol Definition

A protocol is defined by:
- **States** — an enum (e.g., `StIdle`, `StBusy`, `StDone`)
- **Messages** — a tagged union indexed by `(from_state, to_state)`, each variant is a
  state transition edge
- **Agency map** — assigns each state to `ClientAgency`, `ServerAgency`, or `NobodyAgency`
- **State tokens** — runtime reflection of type-level states (needed for codecs)

### Peer Type (the protocol coroutine)

A `Peer` is a free monad / coroutine with these operations:

| Operation | When | What |
|---|---|---|
| **Effect** | Any time | Run a side-effect, then continue |
| **Yield** | We have agency | Send a message, transition, continue |
| **Await** | They have agency | Wait for a message, branch on it |
| **Done** | Nobody has agency | Terminate with a result |
| **YieldPipelined** | We have agency (pipelined) | Send + spawn a Receiver for response, continue immediately |
| **Collect** | Pipeline responses outstanding | Block/poll for a pipelined response |

Agency is enforced statically — only the peer with agency can Yield, only the other can
Await. This makes deadlocks and protocol violations impossible by construction.

**Relative agency**: The same protocol definition works for both client and server — the
framework flips `WeHaveAgency`/`TheyHaveAgency` based on role.

### Driver

The `Driver` runs a `Peer` over a transport:

```
Driver {
  sendMessage :: AgencyProof -> Message -> IO ()
  recvMessage :: AgencyProof -> DecoderState -> IO (SomeMessage, DecoderState)
}
```

- `runPeerWithDriver` — single-threaded loop: Yield → send, Await → recv, Done → return
- `runPipelinedPeerWithDriver` — two threads:
  - **Sender thread** processes Yield/Effect/Collect/Done; on YieldPipelined, sends the
    message and enqueues a Receiver onto a queue
  - **Receiver thread** dequeues Receivers and runs them, pushing collected results back

### Codec

```
Codec {
  encode :: Message -> Bytes
  decode :: StateToken -> IncrementalDecoder SomeMessage
}
```

- **Encode** is a pure function from typed message to bytes
- **Decode** is state-aware (given current state, only accepts valid messages) and
  **incremental** — a three-step coroutine:
  - `DecodePartial(Maybe bytes -> next step)` — needs more input
  - `DecodeDone(message, trailing_bytes)` — success
  - `DecodeFail(error)` — failure
- This design handles the lack of message framing in the multiplexer — the decoder
  consumes exactly as many bytes as it needs from the stream

### Direct Connection (Proof)

`connect` runs two dual peers in lock-step with no transport at all: pattern-matches
`(Yield msg k, Await k')` → passes message directly. Proves the framework is sound.

---

## 4. Connection Manager

### States

```
ReservedOutbound → Unnegotiated(Outbound) → OutboundUni
                                           → OutboundDup → DuplexSt
                                                         → OutboundIdle

Unnegotiated(Inbound) → InboundIdle → InboundSt

Any → Terminating → Terminated
```

- **Provenance**: Inbound vs Outbound
- **DataFlow**: Unidirectional vs Duplex (negotiated during handshake)
- Connections are keyed by **peer address** (not connection ID) — enables simultaneous-open
  detection and connection reuse

### Outbound Connection Flow

1. Peer Selection Governor decides to connect
2. `acquireOutboundConnection`: atomically reserves slot → opens TCP socket → forks
   Connection Handler thread
3. Connection Handler runs the handshake mini-protocol, creates a MuxBearer, writes the
   negotiated result to a promise
4. Connection Manager reads the promise → transitions to OutboundUni or OutboundDup
5. Mini-protocols can now be started on the mux handle

### Inbound Connection Flow

1. Server accept loop calls `accept` on listening socket
2. Immediately calls `includeInboundConnection` (within mask to prevent leaks)
3. Forks Connection Handler (same handshake flow)
4. After negotiation: → InboundIdle
5. When remote peer starts hot protocols: → InboundSt

### Temperature System

Protocols are organized by **temperature** controlling when they activate:

| Temperature | Protocols | When |
|---|---|---|
| Established | keep-alive, peer-sharing | After handshake |
| Warm | *(currently none)* | Warm promotion |
| Hot | chain-sync, block-fetch, tx-submission | Hot promotion |

The Peer Selection Governor drives promotions:
- Cold → Warm: acquires connection, starts established protocols
- Warm → Hot: starts hot protocols
- Hot → Warm: stops hot protocols
- Warm → Cold: releases connection

---

## 5. Handshake Protocol

### Flow

**Client**: encodes local `Versions` map → sends `MsgProposeVersions` → waits for response

**Server**: receives `MsgProposeVersions` → runs `acceptOrRefuse`:
1. Intersects client and server version maps
2. Picks the **greatest common key** (highest mutually-supported version)
3. Decodes remote version data for that version
4. Calls `acceptVersion(localData, remoteData)` to validate compatibility
5. Replies `MsgAcceptVersion` or `MsgRefuse`

**Simultaneous open**: Both sides send `MsgProposeVersions`. Each interprets the incoming
message as `MsgReplyVersions` (same CBOR encoding). Both independently run `acceptOrRefuse`
which is deterministic on the same inputs → both converge on the same choice.

### Version Data Codec

Version parameters go through an intermediate CBOR Term representation via
`VersionDataCodec { encodeData, decodeData }`. The version map keys must be encoded in
ascending order. Unrecognized version numbers are skipped gracefully.

---

## 6. ChainSync Protocol

### Client DSL

The client is a free-monad-style DSL with three state types:

- **ClientStIdle** — choose: request next, find intersection, or done
- **ClientStNext** — two callbacks: `recvMsgRollForward(header, tip)` or
  `recvMsgRollBackward(point, tip)`
- **ClientStIntersect** — two callbacks: `recvMsgIntersectFound(point, tip)` or
  `recvMsgIntersectNotFound(tip)`

When the server sends `MsgAwaitReply`, the client runs a user-supplied "await action"
(e.g., do local work while waiting).

### Codec Detail

- Points list in `MsgFindIntersect` uses indefinite-length CBOR for non-empty, definite
  `encodeListLen 0` for empty
- Decoding is **state-aware**: tag 0 (`MsgRequestNext`) only accepted in StIdle, tag 1
  (`MsgAwaitReply`) only in StNext(CanAwait)

### Limits

- Byte limits: `smallByteLimit` (65,535) for all states
- Time limits: idle = configurable (default 3673s), intersect = 10s, can-await = 10s,
  must-reply = random 601-911s (untrusted peers)

---

## 7. BlockFetch Protocol

### Codec

All messages are `[listLen, tag, ...payload]`. Decoder dispatches on
`(current_state, tag, listLen)` triple.

### Limits

- StStreaming gets `largeByteLimit` (2,500,000) since blocks are big
- StIdle/StBusy get `smallByteLimit` (65,535)
- StIdle waits forever, StBusy/StStreaming use `longWait` (60s)

---

## 8. TxSubmission Protocol

### Pull-Based Design

This protocol is **server-driven** — the server (transaction consumer) has agency in StIdle
and requests tx IDs/txs from the client (provider). This inverts the typical pattern and
enables the consumer to apply backpressure.

### Blocking vs Non-Blocking

- **Blocking** (`MsgRequestTxIdsBlocking`): MUST be used when zero unacknowledged tx IDs
  remain. Response MUST be non-empty. No timeout — can wait forever for new txs. Only state
  from which `MsgDone` can be sent.
- **Non-Blocking** (`MsgRequestTxIdsNonBlocking`): MUST be used when there are outstanding
  unacknowledged IDs. Response may be empty. Has a timeout (10s).

The server can pipeline: interleave non-blocking ID requests with tx download requests for
throughput.

### FIFO Acknowledgment

Outstanding tx IDs form a notional FIFO. `ack` acknowledges from the front, `req` requests
more appended. Both are Word16.

### Annotated Codec

The implementation supports an **annotated variant** that preserves raw bytes alongside
decoded values (via `WithBytes`/`WithByteSpan`). This lets the node forward serialized tx
bytes without re-encoding — important for performance.

### Codec Detail

Inner lists (txIdList, txList, txIdsAndSizes) all use **indefinite-length CBOR encoding**.

> **Note**: This confirms the spec's position on indefinite-length for `txIdsAndSizes`.
> The Blueprint's claim of definite-length appears to be incorrect. See the open question
> in `docs/praos-network.md`.

---

## 9. KeepAlive Protocol

- `Cookie` is a Word16 newtype
- Client validates the response cookie matches — mismatch is a protocol error
  (`KeepAliveCookieMissmatch`)
- Time limits: StClient = 97s, StServer = 60s
- There's an open issue (#2505) suggesting StServer should be 10s

---

## 10. PeerSharing Protocol

- `PeerSharingAmount` is Word8 (max 255 peers per request)
- Peer list: empty = `encodeListLen 0`; non-empty = **indefinite-length** CBOR
- IPv6 encoding zeroes out flow info and scope ID
- Unix sockets are explicitly forbidden
- Size limit 5,760 bytes — designed to fit in a single RTT (4 x 1440 TCP segments)

---

## 11. Cross-Cutting Patterns

### Uniform CBOR Framing

Every message across all protocols is `[tag, ...fields]` as a CBOR array. The decoder
always reads the array length then the tag, dispatching on `(state, tag, len)`.

### State-Aware Decoding

Decoders receive the current protocol state and only accept messages valid in that state.
Invalid messages produce protocol errors → connection teardown.

### Parametric Codecs

Block, point, txid, tx, header, tip, and peer address encoders/decoders are injected as
function parameters. The protocol codec itself is type-agnostic — the networking layer
doesn't know about Cardano eras.

### Per-State Limits

Each protocol defines per-state byte limits and timeouts:
- Large data states (streaming blocks, tx lists) → `largeByteLimit` (2,500,000)
- Control messages → `smallByteLimit` (65,535)
- Blocking/waiting states → no timeout or very long
- Response states → bounded timeout

### No Mux-Level Flow Control

The mux has no credit-based flow control. Backpressure is reactive:
- Egress: soft-blocks sender at ~256KB
- Ingress: **hard-kills connection** on buffer overflow (protocol violation)
- Per-protocol flow control (e.g., TxSubmission's FIFO) handles application-level pacing

### STM Coordination

All connection manager state transitions are atomic STM transactions. Promises
(write-once vars) communicate handshake results between handler threads and the manager.
