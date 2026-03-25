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

## LeiosNotify (protocol ID 18) — Phase 4a

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

## LeiosFetch (protocol ID 19) — Phase 4b

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
