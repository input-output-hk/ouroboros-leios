# Security Audit

Per-protocol audit of untrusted-input handling. Each protocol is checked against
the checklist from CLAUDE.md before marking a phase complete.

## Checklist

1. **Allocation bounds** — every length field read from the wire must be checked
   against a maximum before allocating
2. **Buffer bounds** — every accumulation buffer must have a hard cap
3. **No blocking on untrusted input** — demuxer uses `try_send`, never blocks on
   a slow consumer
4. **Timeout coverage** — every state where we wait for remote data has a timeout
5. **Error propagation** — every error results in clean connection teardown
6. **No panics** — no `unwrap()`, `expect()`, indexing without bounds in non-test code

Items 3–6 are enforced structurally by the mux/codec/Runner framework and apply
to all protocols. Per-protocol audits focus on items 1–2 (allocation and buffer
bounds) since those depend on message-specific decode logic.

### Framework-level protections (all protocols)

| Layer | Protection | Limit |
|---|---|---|
| Mux ingress | per-protocol ingress buffer cap | `ingress_limit` per `ProtocolConfig` |
| Codec buffer | `CodecRecv::max_buffer` rejects if accumulated bytes exceed cap | default 2,500,000 bytes |
| Mux demuxer | `try_send` — never blocks on slow protocol consumer | — |
| Runner | `timeout()` applied to `recv()` when remote has agency | per-state `Duration` |
| Runner | `transition()` validates every message against current state | — |
| Mux supervisor | any task failure aborts entire peer connection | — |

---

## Handshake (protocol ID 0)

**Constants:**
- `SIZE_LIMIT = 5_760`
- `TIMEOUT = 10s`

**Allocation bounds:**

| Decode path | Field | Max | Check location |
|---|---|---|---|
| `decode_version_table` | map length | 256 | `MAX_VERSION_TABLE_ENTRIES` check before `Vec::with_capacity` |
| `decode_version_table` | per-entry raw bytes | bounded by `SIZE_LIMIT` | `d.input().get(start..end)` safe slice |
| `decode_refuse_reason` (VersionMismatch) | version list length | 256 | `MAX_MISMATCH_VERSIONS` check before `Vec::with_capacity` |

**Timeout coverage:**

| State | Agency | Timeout |
|---|---|---|
| `StPropose` | Server | 10s |
| `StConfirm` | Server | 10s |
| `StDone` | Nobody | None (terminal) |

**Other checks:**
- Unknown message tags → `DecodeError`
- Truncated messages → minicbor `DecodeError`
- No `unwrap()`/`expect()`/indexing in non-test code

**Test coverage:**
- `oversized_version_table_rejected` — verifies `MAX_VERSION_TABLE_ENTRIES` rejection

**Verdict:** No DOS vectors identified.

---

## ChainSync (protocol ID 2)

**Constants:**
- `INGRESS_LIMIT = 462_000`
- `SIZE_LIMIT = 65_535`
- `TIMEOUT_IDLE = 3673s`
- `TIMEOUT_CAN_AWAIT = 10s`
- `TIMEOUT_MUST_REPLY = 756s`
- `TIMEOUT_INTERSECT = 10s`

**Allocation bounds:**

| Decode path | Field | Max | Check location |
|---|---|---|---|
| `MsgFindIntersect` | points array length | 2,048 | `decode_points` checks `MAX_POINTS` (definite + indefinite) |
| `MsgRollForward` | header bytes | 65,535 | `WrappedHeader::decode` checks `MAX_HEADER_SIZE` |
| `MsgRollForward` / `MsgRollBackward` | tip point hash | exactly 32 | `decode_hash32` rejects != 32 |
| `MsgIntersectFound` | point hash | exactly 32 | `decode_hash32` rejects != 32 |

**Timeout coverage:**

| State | Agency | Timeout |
|---|---|---|
| `StIdle` | Client | None (we have agency) |
| `StCanAwait` | Server | 10s |
| `StMustReply` | Server | 756s |
| `StIntersect` | Server | 10s |
| `StDone` | Nobody | None (terminal) |

**Other checks:**
- Unknown message tags → `DecodeError`
- Truncated messages → minicbor `DecodeError`
- Indefinite CBOR arrays → bounded iteration with max count checks (`decode_points`)
- No `unwrap()`/`expect()`/indexing in non-test code

**Test coverage:**
- `decode_points_oversized_rejected` — verifies `MAX_POINTS` rejection (in types module)

**Verdict:** No DOS vectors identified.

---

## BlockFetch (protocol ID 3)

**Constants:**
- `INGRESS_LIMIT = 230_686_940` (~220 MB)
- `SIZE_LIMIT_SMALL = 65_535` (idle/busy states)
- `SIZE_LIMIT_STREAMING = 2_500_000` (streaming state)
- `TIMEOUT_BUSY = 60s`
- `TIMEOUT_STREAMING = 60s`

**Allocation bounds:**

| Decode path | Field | Max | Check location |
|---|---|---|---|
| `MsgBlock` | block body bytes | 2,500,000 | `BlockBody::decode` checks `MAX_BLOCK_SIZE` |
| `MsgRequestRange` | from/to point hash | exactly 32 | `decode_hash32` rejects != 32 |

**Timeout coverage:**

| State | Agency | Timeout |
|---|---|---|
| `StIdle` | Client | None (we have agency) |
| `StBusy` | Server | 60s |
| `StStreaming` | Server | 60s |
| `StDone` | Nobody | None (terminal) |

**State-dependent size limits:**
- `StIdle`, `StBusy` → 65,535 (requests/status are small)
- `StStreaming` → 2,500,000 (block bodies can be large)

**Other checks:**
- Unknown message tags → `DecodeError`
- Truncated messages → minicbor `DecodeError`
- No `unwrap()`/`expect()`/indexing in non-test code

**Verdict:** No DOS vectors identified.

---

## TxSubmission (protocol ID 4)

**Constants:**
- `INGRESS_LIMIT = 721_424`
- `SIZE_LIMIT_SMALL = 5_760` (control messages)
- `SIZE_LIMIT_LARGE = 2_500_000` (tx delivery)
- `TIMEOUT_NON_BLOCKING = 10s`
- `TIMEOUT_TXS = 10s`
- `MAX_UNACKED = 10`
- `MAX_TX_ID_SIZE = 128`
- `MAX_TX_SIZE = 2_500_000`

**Allocation bounds:**

| Decode path | Field | Max | Check location |
|---|---|---|---|
| `TxId::decode` | tx id bytes | 128 | `MAX_TX_ID_SIZE` check before `.to_vec()` |
| `TxBody::decode` | tx body bytes | 2,500,000 | `MAX_TX_SIZE` check before `.to_vec()` |
| `MsgReplyTxIds` | list length | 10 | `decode_bounded_list` checks `MAX_UNACKED` (definite + indefinite) |
| `MsgRequestTxs` | list length | 10 | `decode_bounded_list` checks `MAX_UNACKED` (definite + indefinite) |
| `MsgReplyTxs` | list length | 10 | `decode_bounded_list` checks `MAX_UNACKED` (definite + indefinite) |

**Timeout coverage:**

| State | Agency | Timeout |
|---|---|---|
| `StInit` | Client | None (we send immediately) |
| `StIdle` | Server | None (server decides pacing) |
| `StTxIdsBlocking` | Client | None (intentional — client blocks waiting for txs) |
| `StTxIdsNonBlocking` | Client | 10s |
| `StTxs` | Client | 10s |
| `StDone` | Nobody | None (terminal) |

**Other checks:**
- Unknown message tags → `DecodeError`
- Truncated messages → minicbor `DecodeError`
- Indefinite CBOR arrays → bounded iteration with max count checks (`decode_bounded_list`)
- `TxId`/`TxBody` use `d.skip()` to measure raw CBOR size before allocating
- No `unwrap()`/`expect()`/indexing in non-test code

**Verdict:** No DOS vectors identified.

---

## KeepAlive (protocol ID 8)

**Constants:**
- `INGRESS_LIMIT = 1_408`
- `SIZE_LIMIT = 65_535`
- `TIMEOUT_CLIENT = 97s`
- `TIMEOUT_SERVER = 60s`

**Allocation bounds:**

No variable-length allocations — messages contain only fixed-size fields (u32 tag, u16 cookie).

**Timeout coverage:**

| State | Agency | Timeout |
|---|---|---|
| `StClient` | Client | 97s |
| `StServer` | Server | 60s |
| `StDone` | Nobody | None (terminal) |

**Other checks:**
- Unknown message tags → `DecodeError`
- Truncated messages → minicbor `DecodeError`
- No `unwrap()`/`expect()`/indexing in non-test code

**Verdict:** No DOS vectors identified.

---

## PeerSharing (protocol ID 10)

**Constants:**
- `INGRESS_LIMIT = 5_760`
- `SIZE_LIMIT = 5_760`
- `MAX_PEERS = 255`
- `TIMEOUT_BUSY = 60s`

**Allocation bounds:**

| Decode path | Field | Max | Check location |
|---|---|---|---|
| `MsgSharePeers` | peer list length | 255 | `MAX_PEERS` check before `Vec::with_capacity` (definite + indefinite) |
| `PeerAddress::decode` | IPv4 / IPv6 | fixed-size | 4 bytes / 16 bytes, no variable allocation |

**Timeout coverage:**

| State | Agency | Timeout |
|---|---|---|
| `StIdle` | Client | None (we have agency) |
| `StBusy` | Server | 60s |
| `StDone` | Nobody | None (terminal) |

**Other checks:**
- Unknown message tags → `DecodeError`
- Unknown peer address tags → `DecodeError`
- Truncated messages → minicbor `DecodeError`
- No `unwrap()`/`expect()`/indexing in non-test code

**Test coverage:**
- `truncated_request_fails` — verifies truncation handling
- `unknown_peer_address_tag_fails` — verifies unknown address type rejection

**Verdict:** No DOS vectors identified.

---

## LeiosNotify (protocol ID 18)

**Constants:**
- `INGRESS_LIMIT = 65_536`
- `SIZE_LIMIT = 65_535`
- `MAX_VOTES_OFFERED = 1_024`
- `MAX_VOTER_ID_SIZE = 256`
- `TIMEOUT_BUSY = 60s`

**Allocation bounds:**

| Decode path | Field | Max | Check location |
|---|---|---|---|
| `MsgLeiosBlockAnnouncement` | header bytes | 65,535 | `WrappedHeader::decode` (`MAX_HEADER_SIZE`) |
| `MsgLeiosBlockOffer` | hash | exactly 32 | `decode_hash32` rejects != 32 |
| `MsgLeiosBlockTxsOffer` | hash | exactly 32 | `decode_hash32` rejects != 32 |
| `MsgLeiosVotesOffer` | vote list length | 1,024 | `decode_vote_offers` checks before alloc (definite) and during iteration (indefinite) |
| `MsgLeiosVotesOffer` | voter ID bytes | 256 | `decode_vote_offer_pair` checks before `.to_vec()` |

**Timeout coverage:**

| State | Agency | Timeout |
|---|---|---|
| `StIdle` | Client | None (we have agency) |
| `StBusy` | Server | 60s |
| `StDone` | Nobody | None (terminal) |

**Other checks:**
- Unknown message tags → `DecodeError`
- Truncated messages → minicbor `DecodeError`
- Indefinite CBOR arrays → bounded iteration with max count checks
- No `unwrap()`/`expect()`/indexing in non-test code

**Test coverage:**
- `votes_offer_exceeds_max_fails` — verifies `MAX_VOTES_OFFERED` rejection
- `wrong_hash_length_fails` — verifies hash length enforcement
- `unknown_tag_fails` — verifies unknown tag rejection
- `truncated_block_offer_fails` — verifies truncation handling
- `decode_indefinite_outer_array` — verifies indefinite array support

**Verdict:** No DOS vectors identified.

---

## LeiosFetch (protocol ID 19)

**Constants:**
- `INGRESS_LIMIT = 16_777_216` (16 MB)
- `SIZE_LIMIT_SMALL = 65_535` (request states)
- `SIZE_LIMIT_LARGE = 16_777_216` (delivery states)
- `MAX_BLOCK_SIZE = 16_777_216`
- `MAX_BITMAP_ENTRIES = 1_024`
- `MAX_TRANSACTIONS = 65_536`
- `MAX_TRANSACTION_SIZE = 65_536`
- `MAX_VOTES = 1_024`
- `MAX_VOTER_ID_SIZE = 256`
- `MAX_VOTE_SIZE = 1_024`
- `TIMEOUT_SERVER = 120s`

**Allocation bounds:**

| Decode path | Field | Max | Check location |
|---|---|---|---|
| `MsgLeiosBlockRequest` | hash | exactly 32 | `decode_hash32` rejects != 32 |
| `MsgLeiosBlock` | block bytes | 16 MB | `decode_block` checks before `.to_vec()` |
| `MsgLeiosBlockTxsRequest` | hash | exactly 32 | `decode_hash32` |
| `MsgLeiosBlockTxsRequest` | bitmap entries | 1,024 | `decode_bitmap` checks before insert (definite + indefinite) |
| `MsgLeiosBlockTxs` | tx list length | 65,536 | `decode_blob_list` checks before alloc |
| `MsgLeiosBlockTxs` | per-tx size | 65,536 | `decode_bounded_bytes` checks before `.to_vec()` |
| `MsgLeiosVotesRequest` | vote ID list length | 1,024 | `decode_vote_id_list` checks before alloc |
| `MsgLeiosVotesRequest` | voter ID size | 256 | `decode_vote_id_pair` checks before `.to_vec()` |
| `MsgLeiosVoteDelivery` | vote list length | 1,024 | `decode_blob_list` checks before alloc |
| `MsgLeiosVoteDelivery` | per-vote size | 1,024 | `decode_bounded_bytes` checks before `.to_vec()` |
| `MsgLeiosBlockRangeRequest` | start/end hash | exactly 32 | `decode_hash32` |
| `MsgLeiosNextBlockAndTxsInRange` | block bytes | 16 MB | `decode_block` |
| `MsgLeiosNextBlockAndTxsInRange` | tx list | 65,536 count, 65,536/item | `decode_blob_list` + `decode_bounded_bytes` |
| `MsgLeiosLastBlockAndTxsInRange` | block bytes | 16 MB | `decode_block` |
| `MsgLeiosLastBlockAndTxsInRange` | tx list | 65,536 count, 65,536/item | `decode_blob_list` + `decode_bounded_bytes` |

**Timeout coverage:**

| State | Agency | Timeout |
|---|---|---|
| `StIdle` | Client | None (we have agency) |
| `StBlock` | Server | 120s |
| `StBlockTxs` | Server | 120s |
| `StVotes` | Server | 120s |
| `StBlockRange` | Server | 120s |
| `StDone` | Nobody | None (terminal) |

**State-dependent size limits:**
- `StIdle` → 65,535 (requests are small)
- `StBlock`, `StBlockTxs`, `StVotes`, `StBlockRange` → 16 MB (deliveries can be large)

**Other checks:**
- Unknown message tags → `DecodeError`
- Truncated messages → minicbor `DecodeError`
- Indefinite CBOR arrays and maps → bounded iteration with max count checks
- Bitmap uses `BTreeMap` — duplicate keys overwrite (no amplification)
- No `unwrap()`/`expect()`/indexing in non-test code

**Test coverage:**
- `bitmap_exceeds_max_fails` — verifies `MAX_BITMAP_ENTRIES` rejection
- `transaction_list_exceeds_max_fails` — verifies `MAX_TRANSACTIONS` rejection
- `vote_delivery_exceeds_max_fails` — verifies `MAX_VOTES` rejection
- `vote_request_exceeds_max_fails` — verifies vote request list rejection
- `wrong_hash_length_fails` — verifies hash length enforcement
- `unknown_tag_fails` — verifies unknown tag rejection
- `truncated_message_fails` — verifies truncation handling
- `decode_indefinite_outer_array` — verifies indefinite array support

**Verdict:** No DOS vectors identified.

---

## HeaderInfo parser (types.rs)

**Design:** `HeaderInfo::parse()` navigates the Shelley+ header CBOR structure to
extract common fields (slot, block_number, issuer, etc.) plus optional Leios
extensions. Returns `None` (not error) for Byron headers or any parse failure.

**Allocation bounds:**

| Decode path | Field | Max | Check location |
|---|---|---|---|
| Outer array | era tag | u8 (from u32) | `try_parse` |
| `#6.24` tag | inner bytes | bounded by `MAX_HEADER_SIZE` (65,535) at mux level | `WrappedHeader::decode` |
| `prev_hash` | hash | exactly 32 or null | `parse_optional_hash` |
| `issuer_vkey` | hash | exactly 32 | `parse_hash32` |
| `block_body_hash` | hash | exactly 32 | `parse_hash32` |
| `announced_eb` | hash | exactly 32 | `parse_hash32` |
| `announced_eb_size` | uint | u32 | minicbor `u32()` |
| `certified_eb` | bool | 1 byte | minicbor `bool()` |
| Skipped fields | VRF, cert, version | — | `decoder.skip()` (no allocation) |

**Key safety properties:**
- No allocations from untrusted length fields — all decoded values are fixed-size
- `decoder.skip()` for fields we don't need — zero allocation, just advances position
- Any decode error → returns `None`, no panic
- Byron headers (era 0/1) → returns `None` immediately
- Inner bytes bounded by `MAX_HEADER_SIZE` at the mux/codec layer

**Verdict:** No DOS vectors. Parser reads fixed-size fields and skips
variable-size ones without allocating.

---

## Coordinator Leios extensions

Phase 4e adds dedup, offer tracking, and smart fetch routing to the coordinator
for Leios events. All new state is coordinator-internal (not wire data), but is
driven by untrusted peer events.

**Data structures and bounds:**

| Structure | Type | Bound | Behavior at cap |
|---|---|---|---|
| `seen_leios_blocks` | `HashSet<(u64, [u8;32])>` | `MAX_LEIOS_SEEN` (100,000) | Fail-open: forward without dedup |
| `seen_leios_txs` | `HashSet<(u64, [u8;32])>` | `MAX_LEIOS_SEEN` (100,000) | Fail-open: forward without dedup |
| `seen_leios_votes` | `HashSet<(u64, Vec<u8>)>` | `MAX_LEIOS_SEEN` (100,000) | Fail-open: forward without dedup |
| `leios_block_offers` | `HashMap<..., Vec<PeerId>>` | `MAX_LEIOS_OFFERS` (100,000) | Stop tracking new offers |
| `leios_txs_offers` | `HashMap<..., Vec<PeerId>>` | `MAX_LEIOS_OFFERS` (100,000) | Stop tracking new offers |
| `leios_vote_offers` | `HashMap<..., Vec<PeerId>>` | `MAX_LEIOS_OFFERS` (100,000) | Stop tracking new offers |
| `pending_leios_block_fetches` | `HashMap<..., PeerId>` | Bounded by app commands | Cleaned on fetch or peer failure |
| `pending_leios_txs_fetches` | `HashMap<..., PeerId>` | Bounded by app commands | Cleaned on fetch or peer failure |
| `pending_leios_vote_fetches` | `HashMap<..., PeerId>` | Bounded by app commands | Cleaned on fetch or peer failure |

**Allocation bounds:**
- Capacity caps (`MAX_LEIOS_SEEN`, `MAX_LEIOS_OFFERS`) prevent unbounded growth
  regardless of peer behavior (malicious slots, unique hash flooding)
- Slot-based pruning (`update_leios_slot`) handles normal-case eviction; capacity
  caps are the adversarial safety net
- `Vec<PeerId>` in offer maps: deduped before push (bounded by `max_peers`)
- `voter_id` in vote keys: bounded to 256 bytes at codec layer (`MAX_VOTER_ID_SIZE`)

**Blocking:**
- Event handlers use `.send().await` on `network_events` channel (capacity 64).
  This is a pre-existing pattern shared with all Praos event handlers. If the
  application consumer stalls, the coordinator loop blocks. Not addressed here —
  separate concern affecting the entire coordinator, not specific to Phase 4e.

**No panics:**
- No `unwrap()`, `expect()`, or unchecked indexing in production code
- All fallbacks use `unwrap_or()`, `unwrap_or_default()`, or safe patterns

**Error propagation:**
- Channel send failures are silently dropped (`let _ = ...`). This is intentional:
  a closed app channel should not crash the coordinator.

**Verdict:** All coordinator state is capacity-bounded. Dedup degrades gracefully
under adversarial load (fail-open). No new DOS vectors identified.
