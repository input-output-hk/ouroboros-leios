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
