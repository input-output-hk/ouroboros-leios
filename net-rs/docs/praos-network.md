# Praos Network Protocol Reference

Reference extracted from the [Ouroboros Network Specification](https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf) (20 March 2026)
and the [Cardano Blueprint](https://cardano-scaling.github.io/cardano-blueprint/network/index.html).

Only Node-to-Node (N2N) protocols are covered here. Node-to-Client is out of scope for net-rs.

---

## 1. Multiplexer

### 1.1 Overview

All N2N mini-protocols share a single TCP connection per peer pair. The multiplexer segments
each mini-protocol's byte stream into frames, interleaves them on the wire, and reassembles
them on the far side. The bearer must be ordered, reliable, and full-duplex.

### 1.2 Wire Format (Segment Header)

Each segment is prefixed with an 8-byte header, big-endian:

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                      Transmission Time                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|M|     Mini Protocol ID        |        Payload Length n       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                      Payload (n bytes)                        |
```

| Field | Bits | Description |
|---|---|---|
| Transmission Time | 32 | Lower 32 bits of sender's monotonic clock, 1 us resolution |
| M (Mode) | 1 | `0` = initiator (client), `1` = responder (server) |
| Mini Protocol ID | 15 | Protocol number (see table below) |
| Payload Length | 16 | Payload size in bytes. Max = 2^16 - 1 = 65535 |

**Total header: 8 bytes.** Payload follows immediately.

### 1.3 N2N SDU Size Limit

For the Cardano Node N2N protocol, each SDU (segment) has a maximum payload size of **12,288 bytes**.
This is an implementation choice, not a protocol limit.

### 1.4 Mux SDU Timeouts

| Phase | Timeout |
|---|---|
| During handshake | 10s per SDU |
| After handshake | 30s per SDU |

These are bearer-level timeouts bounding how long it takes to receive a complete SDU (leading
edge to trailing edge), not inter-SDU gaps.

### 1.5 Inbound Idleness Timeout

On the inbound (responder) side, a **5s idleness timeout** starts when a connection is accepted
or when all responder mini-protocols have terminated. If it expires without any message from
the remote end, the connection must be closed (unless it is the outbound side of a duplex
connection). After all mini-protocols terminate and idleness expires, the connection gets a
**60s** close timeout.

### 1.6 Fairness

The Haskell implementation uses **round-robin scheduling** across mini-protocols. Each protocol
can transmit at most one segment per turn. If no data is ready, the slot is skipped.
The multiplexer may merge multiple small messages from the same protocol into one segment,
and may avoid splitting small messages across segments. All messages in a segment must belong
to the same mini-protocol.

### 1.7 Demux Ingress Buffers

There is a fixed-size buffer between the demux output and each mini-protocol's input. Overflow
is a protocol violation and causes connection teardown.

| Mini-protocol | Ingress buffer (bytes) |
|---|---|
| Handshake | (single message) |
| Chain-Sync | 462,000 |
| Block-Fetch | 230,686,940 |
| Tx-Submission | 721,424 |
| Keep-Alive | 1,408 |
| Peer-Sharing | 5,760 |

---

## 2. N2N Mini-Protocol Numbers

| Mini-protocol | Protocol ID |
|---|---|
| Handshake | 0 |
| Chain-Sync | 2 |
| Block-Fetch | 3 |
| Tx-Submission | 4 |
| Keep-Alive | 8 |
| Peer-Sharing (optional) | 10 |

---

## 3. N2N Protocol Versions

Currently supported:

| Version | Value | Description |
|---|---|---|
| NodeToNodeV_14 | 14 | Plomin HF, mandatory on mainnet as of 2025-01-29 |
| NodeToNodeV_15 | 15 | Identifies nodes supporting SRV records |

The CDDL version number encoding: `versionNumber_v14_to_v15 = 14 / 15` and
`versionNumber_v16_to_last = 16` (for future).

Historical versions (no longer supported): V1-V13. See Appendix B of the spec for details.

> **Note**: The Blueprint references v13+v14, but the spec (dated 20 Mar 2026) lists v14+v15
> as currently supported and v13 as historical. The spec is more recent — use v14/v15.

---

## 4. Encoding Conventions

All mini-protocol messages are CBOR-encoded. Each message is a CBOR array where the first
element is an integer message tag. The CDDL specs use definite-length arrays and maps
exclusively.

### Common CDDL Base Types

```cddl
block   = any
header  = any
tip     = any
point   = any
points  = [ *point ]    ; definite-length list
txId    = any
tx      = any
slotNo  = word64

word8   = uint .size 1   ; 1 byte
word16  = uint .size 2   ; 2 bytes
word32  = uint .size 4   ; 4 bytes
word64  = uint .size 8   ; 8 bytes
```

The networking layer is polymorphic over blocks, headers, points, txids, etc. The spec
uses `any` for these types; the concrete Cardano encodings are below.

### Concrete Cardano Types (from Blueprint)

**Point** (genesis or slot+hash):
```cddl
point = []                           ; genesis point
      / [ slotNo, hash ]             ; slot number + block header hash
```

**Tip** (point + block number):
```cddl
tip = [ point, blockNo ]
```
where `blockNo` is a uint.

**Era tag wrapper (ns7)** — a 7-variant tagged union for multi-era support.
Tags 0-7 map to Byron(0/1), Shelley(2), Allegra(3), Mary(4), Alonzo(5), Babbage(6), Conway(7).

**Header** (ChainSync uses headers, not full blocks for N2N):
```cddl
header = ns7<byronHeader,
             serialisedShelleyHeader<shelley.header>,
             serialisedShelleyHeader<allegra.header>,
             serialisedShelleyHeader<mary.header>,
             serialisedShelleyHeader<alonzo.header>,
             serialisedShelleyHeader<babbage.header>,
             serialisedShelleyHeader<conway.header>>

byronHeader = [byronRegularIdx, #6.24(bytes .cbor byron.blockhead)]
            / [byronBoundaryIdx, #6.24(bytes .cbor byron.ebbhead)]

byronBoundaryIdx = [0, word32]
byronRegularIdx  = [1, word32]

serialisedShelleyHeader<era> = #6.24(bytes .cbor era)
```

**Block** (BlockFetch sends full blocks):
```cddl
serialisedCardanoBlock = #6.24(bytes .cbor cardanoBlock)

cardanoBlock = byron.block         ; era tags 0 (regular) or 1 (EBB)
             / [2, shelley.block]
             / [3, allegra.block]
             / [4, mary.block]
             / [5, alonzo.block]
             / [6, babbage.block]
             / [7, conway.block]
```

**Transaction ID**:
```cddl
txId = ns7<byronTxId,
           shelley.transaction_id,
           allegra.transaction_id,
           mary.transaction_id,
           alonzo.transaction_id,
           conway.transaction_id,
           babbage.transaction_id>

byronTxId = [0, byron.txid]
          / [1, byron.certificateid]
          / [2, byron.updid]
          / [3, byron.voteid]
```

**Transaction**:
```cddl
tx = ns7<byron.tx,
         serialisedShelleyTx<shelley.transaction>,
         serialisedShelleyTx<allegra.transaction>,
         serialisedShelleyTx<mary.transaction>,
         serialisedShelleyTx<alonzo.transaction>,
         serialisedShelleyTx<babbage.transaction>,
         serialisedShelleyTx<conway.transaction>>

serialisedShelleyTx<era> = #6.24(bytes .cbor era)
```

**CBOR-in-CBOR**: Tag `#6.24` means the payload is a CBOR-encoded byte string. This allows
the networking layer to forward opaque blobs without fully decoding era-specific structures.

**Note on message segmentation**: The multiplexer has no start-of-message flag or N-of-M
counter. There are no framing bits indicating message boundaries within the payload stream.
The receiver must attempt CBOR decoding to determine when a complete message has been
received. This is a known inefficiency noted in both the spec and blueprint.

---

## 5. Handshake Mini-Protocol

**Protocol ID:** 0 (same for N2N and N2C)

### 5.1 Purpose

Negotiates protocol version and parameters. Runs exactly once at connection startup.
Consists of one request from the client and one reply from the server. Handshake messages
are transmitted as single MUX segments (not split) because the multiplexer is not yet
initialized.

### 5.2 State Machine

```
States:  StPropose (Client), StConfirm (Server), StDone (terminal)

start --> StPropose
  StPropose --[MsgProposeVersions]--> StConfirm
  StConfirm --[MsgAcceptVersion]---> StDone
  StConfirm --[MsgReplyVersion]----> StDone    (simultaneous TCP open)
  StConfirm --[MsgRefuse]----------> StDone
```

### 5.3 Messages

| From | Message | Parameters | To |
|---|---|---|---|
| StPropose | **MsgProposeVersions** | versionTable | StConfirm |
| StConfirm | **MsgReplyVersion** | versionTable | StDone |
| StConfirm | **MsgAcceptVersion** | (versionNumber, versionData) | StDone |
| StConfirm | **MsgRefuse** | reason | StDone |

### 5.4 N2N Version Data

The version data record for N2N contains:

| Field | Type | Description |
|---|---|---|
| networkMagic | Word32 | Network identifier (e.g., 764824073 for mainnet) |
| diffusionMode | Bool | `True` = initiator-only, `False` = initiator-and-responder |
| peerSharing | 0 or 1 | 1 = will run PeerSharing mini-protocol |
| query | Bool | `True` = send all versions & terminate |

### 5.5 Version Negotiation Algorithm (Server)

1. Compute intersection of client's and server's supported version numbers
2. If empty: reply `MsgRefuse(VersionMismatch)` with server's supported versions
3. Else: select the **highest** common version number
4. Decode the protocol parameters CBOR for that version
5. If decode fails: `MsgRefuse(HandshakeDecodeError)` with version number and error
6. Test the parameters against server policy
7. If refused: `MsgRefuse(Refused)` with version number and error
8. Compute negotiated parameters and reply `MsgAcceptVersion`

Negotiated version data rules:
- network magic must agree, else negotiation fails
- diffusion mode = initiator-only if **either** side proposes it (logical OR)
- peer sharing inherited from the remote side
- query inherited from the client

### 5.6 Simultaneous TCP Open

Both sides send `MsgProposeVersions`; each interprets the incoming message as
`MsgReplyVersion` (same CBOR encoding). Both choose the highest common version.
The `acceptable` function must be symmetric: `acceptable local remote == acceptable remote local`.

### 5.7 Refuse Reasons

| Tag | CDDL | Meaning |
|---|---|---|
| 0 | `[0, [*versionNumbers]]` | VersionMismatch |
| 1 | `[1, versionNumbers, tstr]` | HandshakeDecodeError |
| 2 | `[2, versionNumbers, tstr]` | Refused |

### 5.8 CDDL Encoding (N2N, >= v14)

```cddl
handshakeMessage
    = msgProposeVersions
    / msgAcceptVersion
    / msgRefuse
    / msgQueryReply

msgProposeVersions = [0, versionTable]
msgAcceptVersion   = [1, versionNumber_v14_to_v15, v14.nodeToNodeVersionData]
                   / [1, versionNumber_v16_to_last, v16.nodeToNodeVersionData]
msgRefuse          = [2, refuseReason]
msgQueryReply      = [3, versionTable]

versionTable = { * versionNumber_v14_to_v15 => v14.nodeToNodeVersionData
               , * versionNumber_v16_to_last => v16.nodeToNodeVersionData
               }

versionNumber_v14_to_v15 = 14 / 15
versionNumber_v16_to_last = 16

refuseReason
    = refuseReasonVersionMismatch
    / refuseReasonHandshakeDecodeError
    / refuseReasonRefused

refuseReasonVersionMismatch      = [0, [ *versionNumbers ] ]
refuseReasonHandshakeDecodeError = [1, versionNumbers, tstr]
refuseReasonRefused              = [2, versionNumbers, tstr]
```

### 5.9 Size Limits

| State | Max bytes |
|---|---|
| StPropose | 5,760 |
| StConfirm | 5,760 |

### 5.10 Timeouts

| State | Timeout |
|---|---|
| StPropose | 10s |
| StConfirm | 10s |

---

## 6. Chain-Sync Mini-Protocol

**Protocol ID:** 2 (N2N, headers only; N2C uses 5 with full blocks)

### 6.1 Purpose

Replicates the chain of block **headers** from a producer (server/upstream) to a consumer
(client/downstream). The consumer uses these headers with Block-Fetch to download full
blocks. The protocol supports finding an intersection point for initial sync and following
the tip with producer-driven updates.

### 6.2 State Machine

```
States:
  StIdle       (Client)  - consumer can request next or find intersection
  StCanAwait   (Server)  - producer can reply with data or say "wait"
  StMustReply  (Server)  - producer must reply (no AwaitReply allowed)
  StIntersect  (Server)  - producer searches for intersection point
  StDone       (terminal)

start --> StIdle

  StIdle --[MsgRequestNext]-----> StCanAwait
  StIdle --[MsgFindIntersect]---> StIntersect
  StIdle --[MsgDone]------------> StDone

  StCanAwait --[MsgAwaitReply]---> StMustReply
  StCanAwait --[MsgRollForward]--> StIdle
  StCanAwait --[MsgRollBackward]-> StIdle

  StMustReply --[MsgRollForward]--> StIdle
  StMustReply --[MsgRollBackward]-> StIdle

  StIntersect --[MsgIntersectFound]----> StIdle
  StIntersect --[MsgIntersectNotFound]-> StIdle
```

### 6.3 Messages

| From | Message | Parameters | To |
|---|---|---|---|
| StIdle | **MsgRequestNext** | | StCanAwait |
| StIdle | **MsgFindIntersect** | [point] | StIntersect |
| StIdle | **MsgDone** | | StDone |
| StCanAwait | **MsgAwaitReply** | | StMustReply |
| StCanAwait | **MsgRollForward** | header, tip | StIdle |
| StCanAwait | **MsgRollBackward** | point_old, tip | StIdle |
| StMustReply | **MsgRollForward** | header, tip | StIdle |
| StMustReply | **MsgRollBackward** | point_old, tip | StIdle |
| StIntersect | **MsgIntersectFound** | point_intersect, tip | StIdle |
| StIntersect | **MsgIntersectNotFound** | tip | StIdle |

### 6.4 Protocol Flow

**Downloading (consumer behind):** Consumer sends `MsgRequestNext` repeatedly. Producer
replies with `MsgRollForward(header, tip)` for each block. This continues until the
read-pointer reaches the chain tip.

**At the tip (producer-driven):** When the consumer is caught up, the producer sends
`MsgAwaitReply` (no new data yet). The state moves to StMustReply. When a new block
arrives, the producer sends `MsgRollForward`.

**Finding intersection:** Consumer sends `MsgFindIntersect` with a list of known points
(ordered by preference, highest slot first). Producer replies with `MsgIntersectFound`
(the best known point) or `MsgIntersectNotFound`. For efficiency, use a binary search
pattern: `[point(b), point(b-1), point(b-2), point(b-4), point(b-8), ...]`.

**Fork handling:** If the producer switches to a new fork, the read-pointer is moved to the
last common block and the next reply is `MsgRollBackward(point, tip)`.

### 6.5 CDDL Encoding

```cddl
chainSyncMessage
    = msgRequestNext
    / msgAwaitReply
    / msgRollForward
    / msgRollBackward
    / msgFindIntersect
    / msgIntersectFound
    / msgIntersectNotFound
    / chainSyncMsgDone

msgRequestNext       = [0]
msgAwaitReply        = [1]
msgRollForward       = [2, header.header, tip]   ; header is era-wrapped (see sec 4)
msgRollBackward      = [3, point, tip]
msgFindIntersect     = [4, points]
msgIntersectFound    = [5, point, tip]
msgIntersectNotFound = [6, tip]
chainSyncMsgDone     = [7]
```

### 6.6 Size Limits (N2N)

| State | Max bytes |
|---|---|
| StIdle | 65,535 |
| StCanAwait | 65,535 |
| StMustReply | 65,535 |
| StIntersect | 65,535 |

### 6.7 Timeouts (N2N)

| State | Timeout |
|---|---|
| StIdle | 3,673s |
| StCanAwait | 10s |
| StMustReply | random between 601s and 911s (untrusted peers) |
| StIntersect | 10s |

The StMustReply timeout only applies to untrusted peers. Trusted peers are assumed honest
and will send headers as they become available.

---

## 7. Block-Fetch Mini-Protocol

**Protocol ID:** 3

### 7.1 Purpose

Downloads ranges of full blocks by point (slot + hash). The client requests a range and the
server streams back the blocks. Supports pipelining: the client can send multiple
`MsgRequestRange` messages without waiting for responses.

### 7.2 State Machine

```
States:
  StIdle      (Client)  - can request a range or terminate
  StBusy      (Server)  - server decides if it has the blocks
  StStreaming (Server)  - server streams blocks
  StDone      (terminal)

start --> StIdle

  StIdle --[MsgRequestRange]-> StBusy
  StIdle --[MsgClientDone]---> StDone

  StBusy --[MsgStartBatch]--> StStreaming
  StBusy --[MsgNoBlocks]----> StIdle

  StStreaming --[MsgBlock]-----> StStreaming
  StStreaming --[MsgBatchDone]-> StIdle
```

### 7.3 Messages

| From | Message | Parameters | To |
|---|---|---|---|
| StIdle | **MsgRequestRange** | range (point, point) | StBusy |
| StIdle | **MsgClientDone** | | StDone |
| StBusy | **MsgNoBlocks** | | StIdle |
| StBusy | **MsgStartBatch** | | StStreaming |
| StStreaming | **MsgBlock** | body | StStreaming |
| StStreaming | **MsgBatchDone** | | StIdle |

The range in `MsgRequestRange` is **inclusive on both sides** (from-point, to-point).

### 7.4 CDDL Encoding

```cddl
blockFetchMessage
    = msgRequestRange
    / msgClientDone
    / msgStartBatch
    / msgNoBlocks
    / msgBlock
    / msgBatchDone

msgRequestRange = [0, point, point]
msgClientDone   = [1]
msgStartBatch   = [2]
msgNoBlocks     = [3]
msgBlock        = [4, block]
msgBatchDone    = [5]
```

### 7.5 Size Limits

| State | Max bytes |
|---|---|
| StIdle | 65,535 |
| StBusy | 65,535 |
| StStreaming | 2,500,000 |

### 7.6 Timeouts

| State | Timeout |
|---|---|
| StIdle | - (none) |
| StBusy | 60s |
| StStreaming | 60s |

---

## 8. Tx-Submission Mini-Protocol (v2)

**Protocol ID:** 4 (version 2, used since NodeToNodeV_6)

### 8.1 Purpose

Pull-based transaction dissemination between full nodes. The server (transaction consumer)
asks the client (transaction provider) for transaction IDs, then selectively requests full
transactions. Designed for high throughput with flow control, preventing resource exhaustion
attacks.

### 8.2 State Machine

```
States:
  StInit             (Client)  - send MsgInit to start
  StIdle             (Server)  - server requests tx ids
  StTxIdsBlocking    (Client)  - client provides tx ids (blocking)
  StTxIdsNonBlocking (Client)  - client provides tx ids (non-blocking)
  StTxs              (Client)  - client provides full transactions
  StDone             (terminal)

start --> StInit

  StInit --[MsgInit]--------------------> StIdle

  StIdle --[MsgRequestTxIdsNonBlocking]-> StTxIdsNonBlocking
  StIdle --[MsgRequestTxIdsBlocking]----> StTxIdsBlocking
  StIdle --[MsgRequestTxs]--------------> StTxs

  StTxIdsNonBlocking --[MsgReplyTxIds]--> StIdle
  StTxIdsBlocking    --[MsgReplyTxIds]--> StIdle
  StTxIdsBlocking    --[MsgDone]--------> StDone

  StTxs --[MsgReplyTxs]-> StIdle
```

### 8.3 Messages

| From | Message | Parameters | To |
|---|---|---|---|
| StInit | **MsgInit** | | StIdle |
| StIdle | **MsgRequestTxIdsNonBlocking** | ack, req | StTxIdsNonBlocking |
| StIdle | **MsgRequestTxIdsBlocking** | ack, req | StTxIdsBlocking |
| StTxIdsNonBlocking | **MsgReplyTxIds** | [(id, size)] | StIdle |
| StTxIdsBlocking | **MsgReplyTxIds** | [(id, size)] | StIdle |
| StIdle | **MsgRequestTxs** | [ids] | StTxs |
| StTxs | **MsgReplyTxs** | [txs] | StIdle |
| StTxIdsBlocking | **MsgDone** | | StDone |

### 8.4 Flow Control Details

- `ack` (Word16): number of previously-announced tx ids to acknowledge (remove from FIFO)
- `req` (Word16): max number of new tx ids requested
- Either `ack` or `req` MUST be non-zero
- `req` MUST NOT put total outstanding over the protocol limit
- **Max unacknowledged tx ids: 10** (protocol error to exceed)
- Blocking request: reply MUST have at least 1 tx id; client blocks until available
- Non-blocking request: reply may be empty; MUST be used if there are unacked tx ids
- `MsgReplyTxIds` returns pairs of (txId, txSizeInBytes) where size is Word32
- `MsgRequestTxs` may only request previously announced, outstanding, not-yet-requested ids
- `MsgReplyTxs` may omit transactions that became invalid; omitted ids treated as never announced

### 8.5 CDDL Encoding

```cddl
txSubmission2Message
    = msgInit
    / msgRequestTxIds    ; covers both blocking and non-blocking
    / msgReplyTxIds
    / msgRequestTxs
    / msgReplyTxs
    / tsMsgDone

msgInit          = [6]
msgRequestTxIds  = [0, tsBlocking, txCount, txCount]
msgReplyTxIds    = [1, txIdsAndSizes]
msgRequestTxs    = [2, txIdList]
msgReplyTxs      = [3, txList]
tsMsgDone        = [4]

tsBlocking    = false / true
txCount       = word16
txIdList      = [ *txId ]       ; indefinite-length per blueprint
txList        = [ *tx ]         ; indefinite-length per blueprint
txIdAndSize   = [txId, txSizeInBytes]
txIdsAndSizes = [ *txIdAndSize] ; definite-length
txSizeInBytes = word32
```

### 8.6 Size Limits

| State | Max bytes |
|---|---|
| StInit | 5,760 |
| StIdle | 5,760 |
| StTxIdsBlocking | 2,500,000 |
| StTxIdsNonBlocking | 2,500,000 |
| StTxs | 2,500,000 |

### 8.7 Timeouts

| State | Timeout |
|---|---|
| StInit | - |
| StIdle | - |
| StTxIdsBlocking | - |
| StTxIdsNonBlocking | 10s |
| StTxs | 10s |

---

## 9. Keep-Alive Mini-Protocol

**Protocol ID:** 8

### 9.1 Purpose

Sends keep-alive messages and measures round-trip time. The cookie allows matching
responses to requests.

### 9.2 State Machine

```
States:
  StClient (Client) - can send keep-alive or terminate
  StServer (Server) - must respond with matching cookie
  StDone   (terminal)

start --> StClient

  StClient --[MsgKeepAlive]---------> StServer
  StClient --[MsgDone]--------------> StDone

  StServer --[MsgKeepAliveResponse]-> StClient
```

### 9.3 Messages

| From | Message | Parameters | To |
|---|---|---|---|
| StClient | **MsgKeepAlive** | cookie (Word16) | StServer |
| StClient | **MsgDone** | | StDone |
| StServer | **MsgKeepAliveResponse** | cookie (Word16) | StClient |

The response cookie **must match** the request cookie. Mismatch is a protocol error.

### 9.4 CDDL Encoding

```cddl
keepAliveMessage = msgKeepAlive
                 / msgKeepAliveResponse
                 / msgDone

msgKeepAlive         = [0, word16]
msgKeepAliveResponse = [1, word16]
msgDone              = [2]
```

### 9.5 Size Limits

| State | Max bytes |
|---|---|
| StClient | 65,535 |
| StServer | 65,535 |

### 9.6 Timeouts

| State | Timeout |
|---|---|
| StClient | 97s |
| StServer | 60s |

---

## 10. Peer-Sharing Mini-Protocol

**Protocol ID:** 10 (optional, from NodeToNodeV_11; requires `peerSharing = 1` in handshake)

### 10.1 Purpose

Simple request-reply protocol for nodes to share their upstream peer addresses (a subset
of Known Peers). Runs indefinitely (termination = error or peer demotion).

### 10.2 State Machine

```
States:
  StIdle (Client) - can request peers or terminate
  StBusy (Server) - must respond with peers
  StDone (terminal)

start --> StIdle

  StIdle --[MsgShareRequest]-> StBusy
  StIdle --[MsgDone]---------> StDone

  StBusy --[MsgSharePeers]---> StIdle
```

### 10.3 Messages

| From | Message | Parameters | To |
|---|---|---|---|
| StIdle | **MsgShareRequest** | amount (Word8) | StBusy |
| StIdle | **MsgDone** | | StDone |
| StBusy | **MsgSharePeers** | [peerAddress] | StIdle |

- Sending more peers than requested is a protocol error
- Server should only share peers it has successfully connected to
- Server must not share known-to-be-ledger peers

### 10.4 Peer Address Format

```cddl
peerAddresses = [* peerAddress]

peerAddress = [0, word32, portNumber]                                    ; IPv4
            / [1, word32, word32, word32, word32, portNumber]            ; IPv6

portNumber = word16
```

### 10.5 CDDL Encoding

```cddl
peerSharingMessage = msgShareRequest
                   / msgSharePeers
                   / msgDone

msgShareRequest = [0, word8]
msgSharePeers   = [1, peerAddresses]
msgDone         = [2]
```

### 10.6 Size Limits

| State | Max bytes |
|---|---|
| StIdle | 5,760 |
| StBusy | 5,760 |

### 10.7 Timeouts

| State | Timeout |
|---|---|
| StIdle | - (none) |
| StBusy | 60s |

---

## 11. Pipelining

Protocol pipelining lets a client send multiple requests without waiting for each response.
It is a client-side optimization that requires no server changes. The MUX/DEMUX layer
guarantees in-order delivery within a mini-protocol, so the client can match responses to
requests by order.

The fixed-size demux ingress buffer limits how many pipelined messages can be outstanding.
A client must never overflow the server's ingress buffer (protocol violation => connection
teardown).

Pipelining is used by all N2N mini-protocol clients **except** Chain-Sync (for general
requests). However, per the Blueprint, Chain-Sync nodes can pipeline **one header** on top
of their current selection to accelerate chain diffusion (announcing a tentative header
before full validation). Block-Fetch clients can send multiple `MsgRequestRange` messages
followed by `MsgClientDone` without waiting for block streams in between.

---

## 12. Protocol State Machine Framework

All mini-protocols follow a typed state machine framework:

- **States** are abstract (promoted types), not runtime values
- Both peers are always in the **same** state
- At each state, exactly one side has **agency** (the right to send)
- The other side must wait for a message
- Terminal state `StDone`: neither side has agency
- If an unexpected message is received: connection is aborted

State machine diagrams in the spec use color:
- Green = client has agency
- Blue = server has agency
- Black = terminal

---

## 13. Misbehavior and Connection Termination (from Blueprint)

Connections should be terminated when a peer misbehaves. Per-protocol misbehavior includes:

**General (all protocols):**
- State machine violation (unexpected message for current state)
- Size limit exceeded
- Timeout exceeded
- Demux ingress buffer overflow

**ChainSync:**
- Invalid headers
- Forks exceeding `k` blocks deep

**BlockFetch:**
- Providing unrequested blocks
- Blocks mismatched to their headers
- Blocks with valid headers but invalid bodies

**TxSubmission:**
- Excessive or insufficient transactions sent/acknowledged
- Zero transaction requests
- Requesting unannounced or already-requested transaction IDs

---

## Appendix: N2N Version History

| Version | Description |
|---|---|
| V1 | Initial |
| V2 | Block size hints |
| V3 | Keep-alive introduced |
| V4 | Diffusion mode in handshake |
| V5 | (undocumented) |
| V6 | Tx-submission v2 |
| V7 | New keep-alive, Alonzo era |
| V8 | Chain-sync & block-fetch pipelining |
| V9 | Babbage era |
| V10 | Full duplex connections |
| V11 | Peer sharing willingness |
| V12 | No observable changes |
| V13 | Disabled peer sharing for buggy V11/V12 and InitiatorOnly nodes |
| **V14** | **Plomin HF, mandatory on mainnet (2025-01-29)** |
| **V15** | **SRV record support** |

---

## Open Questions

### TxSubmission `txIdsAndSizes` list encoding: indefinite or definite length?

The spec and blueprint disagree on the CBOR list encoding for `txIdsAndSizes` in the
TxSubmission v2 protocol:

- **Spec** (sec 3.9.4): comment "The codec only accepts indefinite-length lists" applies to
  `txIdsAndSizes = [ *txIdAndSize ]`
- **Blueprint** (TxSubmission2 page): explicitly states `txIdsAndSizes` uses
  **definite-length** encoding (while `txIdList` uses indefinite-length)

This affects wire encoding: indefinite-length CBOR arrays use `0x9F ... 0xFF` framing,
while definite-length arrays encode the element count upfront (`0x80+n` or `0x98 n` etc.).

**Resolution**: The Haskell implementation (`TxSubmission2/Codec.hs`) uses
`encodeListLenIndef` + `encodeBreak` for all inner lists including `txIdsAndSizes`.
This confirms the **spec is correct** (indefinite-length). The Blueprint's claim of
definite-length appears to be an error in the Blueprint documentation.
