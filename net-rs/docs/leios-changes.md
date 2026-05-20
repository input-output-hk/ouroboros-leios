# Leios Network Protocol Changes

Notes from [CIP-0164](https://cips.cardano.org/cip/CIP-0164) on what Leios adds to the
Praos networking stack, and structural implications for net-rs.

---

## 1. Overview

CIP-0164 ("Linear Leios") extends Praos with:
- **Endorser Blocks (EBs)** — larger blocks containing transaction references, announced via RB headers
- **Votes** — BLS-signed attestations on EBs by a committee
- **Certificates** — aggregated BLS signatures proving quorum (≥75% stake)

There are **no Input Blocks (IBs)** in this spec — the research design's IBs are eliminated
by coupling EB production directly to RB production.

Two new block types, but only two new mini-protocols. Praos protocols are minimally modified.

---

## 2. Praos Protocol Modifications

### ChainSync — RB Header Extensions

The `block_header_body` gains two optional field groups:

```cddl
block_header_body =
  [ ...existing fields...
  , ? ( announced_eb    : hash32      ; hash of EB created by this producer
      , announced_eb_size : uint32    ; EB size in bytes
      )
  , ? certified_eb      : bool        ; this RB certifies the previous RB's EB
  ]
```

**Impact**: ChainSync `MsgRollForward` carries these extended headers. The header codec
must handle optional trailing fields. The `certified_eb` bit lets syncing clients predict
the payload size of `MsgLeiosBlockRangeRequest` replies.

### BlockFetch — RB Body Extension

The ranking block body gains an optional certificate:

```cddl
ranking_block =
  [ ...existing fields...
  , ? eb_certificate : leios_certificate
  ]
```

When an RB includes a certificate, it may contain fewer (or no) standard transactions
since the certified EB's transactions are the primary payload.

**Impact**: BlockFetch `MsgBlock` payloads are potentially larger. The block codec must
handle the optional certificate field.

### TxSubmission — Unchanged

TxSubmission continues unchanged. Mempool capacity expands to `2×(S_RB + S_EB-tx)` to
handle both RB and EB transaction pools, but this is a node-level concern, not protocol.

---

## 3. New Mini-Protocols

### LeiosNotify

Announcement protocol. Server notifies client of available Leios data.

```
States:
  StIdle (Client)  — can request next notification or terminate
  StBusy (Server)  — must send one notification
  StDone (terminal)

  StIdle --[MsgLeiosNotificationRequestNext]--> StBusy

  StBusy --[MsgLeiosBlockAnnouncement]--------> StIdle
  StBusy --[MsgLeiosBlockOffer]---------------> StIdle
  StBusy --[MsgLeiosBlockTxsOffer]------------> StIdle
  StBusy --[MsgLeiosVotesOffer]---------------> StIdle

  StIdle --[MsgDone]--------------------------> StDone
```

Messages:

| Sender | Message | Arguments |
|---|---|---|
| Client→ | MsgLeiosNotificationRequestNext | (none) |
| ←Server | MsgLeiosBlockAnnouncement | RB header announcing an EB |
| ←Server | MsgLeiosBlockOffer | slot, Leios hash |
| ←Server | MsgLeiosBlockTxsOffer | slot, Leios hash |
| ←Server | MsgLeiosVotesOffer | list of (slot, vote-issuer-id) pairs |

### LeiosFetch

Request-response protocol for fetching Leios data. Client-driven, pipelineable.

```
States:
  StIdle       (Client) — can request any Leios data or terminate
  StBlock      (Server) — must deliver an EB
  StBlockTxs   (Server) — must deliver transactions
  StVotes      (Server) — must deliver votes
  StBlockRange (Server) — must deliver certified EBs in sequence
  StDone       (terminal)

  StIdle --[MsgLeiosBlockRequest]--------> StBlock
  StBlock --[MsgLeiosBlock]--------------> StIdle

  StIdle --[MsgLeiosBlockTxsRequest]-----> StBlockTxs
  StBlockTxs --[MsgLeiosBlockTxs]--------> StIdle

  StIdle --[MsgLeiosVotesRequest]--------> StVotes
  StVotes --[MsgLeiosVoteDelivery]-------> StIdle

  StIdle --[MsgLeiosBlockRangeRequest]---> StBlockRange
  StBlockRange --[MsgLeiosNextBlockAndTxsInRange]--> StBlockRange
  StBlockRange --[MsgLeiosLastBlockAndTxsInRange]--> StIdle

  StIdle --[MsgDone]---------------------> StDone
```

Messages:

| Sender | Message | Arguments |
|---|---|---|
| Client→ | MsgLeiosBlockRequest | slot, Leios hash |
| ←Server | MsgLeiosBlock | EB block |
| Client→ | MsgLeiosBlockTxsRequest | slot, hash, map(u16 index → u64 bitmap) |
| ←Server | MsgLeiosBlockTxs | list of transactions |
| Client→ | MsgLeiosVotesRequest | list of (slot, vote-issuer-id) |
| ←Server | MsgLeiosVoteDelivery | list of votes |
| Client→ | MsgLeiosBlockRangeRequest | two slots, two RB header hashes |
| ←Server | MsgLeiosNextBlockAndTxsInRange | EB + all its transactions |
| ←Server | MsgLeiosLastBlockAndTxsInRange | EB + all its transactions |

**Bitmap-based transaction addressing**: `MsgLeiosBlockTxsRequest` uses a map from 16-bit
index to 64-bit bitmap. Each bit selects one of 64 contiguous transactions at offset
`64 × index`. A few hundred bytes can request every transaction in even the largest EB.

---

## 4. New Data Types (CDDL)

### Endorser Block

```cddl
endorser_block =
  [ transaction_references : omap<hash32, uint16> ]  ; tx hash → tx size

; omap = order-preserving map with unique keys
omap<K, V> = {* K => V}
```

### Votes

```cddl
leios_vote = persistent_vote / non_persistent_vote

persistent_vote =
  [ 0                                    ; tag
  , election_id
  , persistent_voter_id
  , endorser_block_hash      : hash32
  , vote_signature            : leios_bls_signature
  ]

non_persistent_vote =
  [ 1                                    ; tag
  , election_id
  , pool_id
  , eligibility_signature     : leios_bls_signature
  , endorser_block_hash       : hash32
  , vote_signature            : leios_bls_signature
  ]
```

### Certificate

```cddl
leios_certificate =
  [ election_id
  , endorser_block_hash       : hash32
  , persistent_voters          : [* persistent_voter_id]
  , nonpersistent_voters       : {* pool_id => leios_bls_signature}
  , aggregated_vote_sig        : leios_bls_signature
  ]
```

### BLS Cryptographic Types

BLS12-381 **MinSig** (small signature, large verification key):

```cddl
leios_bls_verification_key = bytes .size 96   ; compressed G2
leios_bls_signature        = bytes .size 48   ; compressed G1
leios_bls_pop              = bytes .size 96   ; compressed G1
```

Certificate size: ~8 KB with MinSig (vs >12 KB with MinPk).

### Merged Block (N2C only, not needed for net-rs)

A client-facing block format combining RB + certified EB transactions. Out of scope.

---

## 5. Priority and QoS Requirements

### Praos Independence

> "The node implementation must prioritize Praos over Leios."

When a node simultaneously issues an RB and the EB it announces, EB diffusion must not
delay RB diffusion. The RB is strictly more urgent.

### Urgency Inversion

Some Leios messages occasionally need Praos-level priority:
- `MsgLeiosBlockRangeRequest` + its responses carry certified EBs that are as urgent as
  the RBs containing them
- The CIP suggests these could be isolated in a **third Leios mini-protocol** with
  Praos-equal priority if the mux needs per-protocol prioritization

### Freshest-First Delivery

All Leios data is prioritized youngest-over-oldest. Every Leios object has an explicit
age (associated with an EB's slot). Objects beyond a certain age stop being relevant:
- Votes older than ~`L_vote` slots
- EBs beyond the historical chain

### Head-of-Line Blocking

Large EB/transaction replies can block small vote deliveries within LeiosFetch. Mitigations:
- Run two instances of LeiosFetch per peer (one for blocks/txs, one for votes)
- Or add server-side request reordering (not currently in the Cardano mux infrastructure)

---

## 6. Timing Parameters

| Parameter | Symbol | Purpose |
|---|---|---|
| Header diffusion | `L_hdr` | Duration for RB headers to reach ≥95% honest stake |
| Voting period | `L_vote` | Window for committee voting on EBs |
| Diffusion period | `L_diff` | Additional time for network-wide EB availability |
| Equivocation detection | `3×L_hdr` | Three sequential phases of header propagation |

**Total certification delay**: `3×L_hdr + L_vote + L_diff` slots before a certificate can
appear in a subsequent RB.

### OCIN Tracking

Nodes track Operational Certificate Issue Numbers to limit EB announcements per election:
- Accept at most 2 distinct OCINs per election (for equivocation detection)
- Ignore announcements with OCIN below the settled ledger state
- Ignore announcements with OCIN > settled+1

---

## 7. Structural Implications for net-rs

### Must Build In From the Start

1. **Pluggable mux scheduling** — Praos protocols must have higher priority than Leios
   protocols. The multiplexer needs per-protocol priority levels, not just round-robin.
   The CIP explicitly calls this out as a requirement.

2. **Multiple protocol instances** — CIP suggests running 2 instances of LeiosFetch per
   peer (one for bulk, one for votes). The mux must support multiple instances of the same
   protocol ID, or the protocols must use different IDs.

3. **Large message handling** — EBs with all their transactions can be very large. The mux
   must interleave large Leios transfers with small urgent Praos messages without
   head-of-line blocking. This reinforces the need for small SDU sizes (12KB) and proper
   scheduling.

4. **Protocol-agnostic framework** — The mini-protocol framework must make it easy to
   define new protocols (LeiosNotify, LeiosFetch) with the same state machine / codec /
   agency patterns as Praos protocols. Don't hardcode just the 6 Praos protocols.

5. **Pipelining support** — LeiosFetch requires client-side pipelining ("Because the client
   only has agency in one state, it can pipeline its requests for the sake of latency
   hiding"). The framework needs first-class pipelining.

6. **Per-protocol priority levels** — At minimum three levels:
   - High: Praos (ChainSync, BlockFetch, TxSubmission, KeepAlive) + LeiosFetch range requests
   - Medium: LeiosFetch (blocks, txs, votes)
   - Low: LeiosNotify, PeerSharing

7. **Freshest-first within a protocol** — Even within a single protocol, the node may
   want to reorder or prioritize messages by age. The mux can't do this (it doesn't
   understand message semantics), but the protocol driver should support it.

### Can Defer

- Concrete LeiosNotify/LeiosFetch codec implementations (after Praos works)
- BLS cryptographic operations (out of scope for networking)
- OCIN tracking logic (node-level, not protocol-level)
- Vote/certificate aggregation (node-level)
- Merged block format (N2C only)
- Server-side request reordering (may never be needed)

### Open Design Questions

- **Protocol IDs for Leios**: CIP doesn't assign specific mini-protocol numbers yet.
  Will need to be negotiated via handshake version.
- **Three protocols or two**: CIP suggests possibly splitting `MsgLeiosBlockRangeRequest`
  into a third protocol for priority reasons. We should design for easy protocol addition.
- **Interaction with Praos version negotiation**: How does handshake indicate Leios support?
  New version number? New version data field? (Similar to how PeerSharing was added in V11.)
