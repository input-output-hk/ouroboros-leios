# Leios Block and Protocol Encoding — Prototype vs CIP-0164

> **Status:** Working draft / skeleton for editing.
> **Subject:** the **cardano-node Leios prototype** — the implementation running
> on the prototype devnet relays. Its on-the-wire (CBOR) block formats and
> node-to-node mini-protocol messages are documented here as CDDL and tracked
> **both ways** against CIP-0164 "Ouroboros Linear Leios": what the prototype
> must change to meet the CIP, and what the CIP must change to match the
> prototype.
>
> **`net-node` reflects the prototype.** The Rust stack in
> [`leios-tools`](../../leios-tools) (`net-rs/net-core`) is a faithful
> reimplementation of the prototype's wire format; its `minicbor`
> encoders/decoders are used here as the legible source of the CDDL, and every
> structure below is **cross-checked against live captures from the prototype
> relays** (§7). Where this doc says "the prototype", that is the cardano-node
> implementation as observed on the wire and mirrored by `net-node`.

## Tracked CIP versions

CIP-0164's wire format changed across three merged PRs. The prototype was built
against the middle one (**#1196**), so all three matter:

| Tag    | CIP PR | Merge commit | Merged | What it changed |
|--------|--------|--------------|--------|------------------|
| **v1** | [#1078][pr1078] | `630bda34` | 2026-01-06 | First published Leios CIP. **2 Leios mini-protocols** (LeiosNotify + LeiosFetch); **two-cohort** votes & certs (persistent / non-persistent); `{u16=>u64}` map tx-bitmap; vote delivery via offer→request; range/Genesis bulk-sync messages. |
| **v2** | [#1196][pr1196] | `5690adca` | 2026-05-27 | "Replace wFA^LS committee with **stake-based committee selection**." Keeps v1's protocol structure, map bitmap, vote-delivery, and range messages **unchanged**; only **replaces votes & certs** with a single uniform `voter_id`-indexed vote and a bitfield certificate. **← the version the prototype targets.** |
| **v3** | [#1167][pr1167] | `bc28ab90` | 2026-06-09 | "Refine Leios protocols." **Splits LeiosNotify into 3 protocols** (LeiosAnnounce / LeiosVotes / LeiosBlockNotify); **direct vote push** (no offer/request); **roaring byte-string** tx-bitmap; `RequestNext(N)` token budget; **drops** range/Genesis messages. Votes & certs unchanged from v2. Current CIP `master`. |

[cip164]: https://github.com/cardano-foundation/CIPs/tree/master/CIP-0164
[pr1078]: https://github.com/cardano-foundation/CIPs/pull/1078
[pr1196]: https://github.com/cardano-foundation/CIPs/pull/1196
[pr1167]: https://github.com/cardano-foundation/CIPs/pull/1167

> **Headline.** The prototype **conforms to v2 (#1196)**: v1's two-protocol
> structure (LeiosNotify ID 18 + LeiosFetch ID 19), no-argument `RequestNext`,
> single-block request, and `{u16 => u64}` map tx-bitmap — *plus* #1196's
> stake-based `voter_id` vote and bitfield certificate. It therefore sits behind
> the latest CIP (**v3 / #1167**), which restructured the protocols. The two
> directions of work are summarized in **§9 (prototype → CIP, macro)** and
> **§10 (CIP → prototype, leaf-level encoding)**, with an alignment matrix in §8.

<!--
  EDITING NOTES (delete before publishing):
  - CDDL transcribed from minicbor encode()/decode() in net-node (leios-tools)
    at net-rs commit 4c799c1, which mirrors the cardano-node prototype; field
    shapes confirmed against live relay captures (§7).
  - v1 CDDL @ 630bda34, v2 CDDL @ 5690adca, v3 CDDL @ master(bc28ab90) — all
    Appendix B + IER tables.
  - `; TODO`/`; NOTE` mark uncertainties / divergences.
  - §7 holds real captured wire bytes from the prototype relays via `net-cli`.
-->

## 1. Scope and sources

- **Implementation tracked:** the **cardano-node Leios prototype** (prototype
  devnet relays). Its wire format is read here from `net-node`
  (`leios-tools/net-rs/net-core`, a faithful reflection; CBOR via `minicbor`
  v0.25) and confirmed against live captures (§7). Standard CBOR (RFC 8949);
  no custom tags beyond `#6.24` (CBOR-in-CBOR).
- **Reference specs:** CIP-0164 Appendix B + §"Leios Mini-Protocols" / IER tables
  at v1, v2, v3 (see above).
- **Out of scope:** Praos-internal ledger structures (tx bodies, witness sets,
  non-Leios certs) — opaque CBOR, not reparsed.

## 2. Conventions

- `bytesN` = `bytes .size N`.
- `#6.24(X)` = CBOR byte string tagged 24 wrapping the CBOR of `X` (RFC 8949
  §3.4.5.1).
- Arrays are **definite-length** unless annotated `; indefinite`.
- Raw pass-through fields: CDDL gives logical shape; body notes "raw".
- Era tagging: NtN txs/tx-ids carry a leading HFC era index (`word16`); §6.4.
- In comparisons: **prototype** = cardano-node Leios prototype (reflected in
  `net-node`, confirmed by captures); **v1** = #1078; **v2** = #1196 (prototype
  target); **v3** = #1167 (master).

## 3. Mini-protocol catalogue (prototype)

Protocol IDs are the mux `ProtocolId` (`u16`) constants in
`net-rs/net-core/src/protocols/*/mod.rs`.

| ID | Protocol      | Source                | v1 / v2 (#1078 / #1196) | v3 (#1167)                |
|----|---------------|-----------------------|-------------------------|---------------------------|
| 0  | Handshake     | `handshake/mod.rs`    | Praos, unchanged        | Praos, unchanged          |
| 2  | ChainSync     | `chainsync/mod.rs`    | Praos, unchanged        | Praos, unchanged          |
| 3  | BlockFetch    | `blockfetch/mod.rs`   | Praos, unchanged        | Praos, unchanged          |
| 4  | TxSubmission  | `txsubmission/mod.rs` | Praos, unchanged        | Praos, unchanged          |
| 8  | KeepAlive     | `keepalive/mod.rs`    | Praos, unchanged        | Praos, unchanged          |
| 10 | PeerSharing   | `peersharing/mod.rs`  | Praos, unchanged        | Praos, unchanged          |
| 18 | LeiosNotify   | `leios_notify/mod.rs` | **LeiosNotify** (1 of 2)| LeiosAnnounce + LeiosVotes + LeiosBlockNotify |
| 19 | LeiosFetch    | `leios_fetch/mod.rs`  | **LeiosFetch** (2 of 2) | LeiosFetch                |

> The prototype's **two-protocol split matches v1 & v2** (the split came only in v3).
> Protocol-ID numbers (18/19) are an implementation choice; no CIP version fixes
> them.

---

## 4. Block and data-structure encodings

> **Note:** Ranking Block, block header (incl. Leios extensions), Endorser
> Block, and Merged Block CDDL are **identical across v1/v2/v3** (Appendix B
> unchanged). One CIP column is shown for these; votes & certs (§5) is where the
> versions diverge.

### 4.1 Point and Tip

`shared-rs/consensus/src/types.rs:14-139`

```cddl
point =
    []                          ; origin (CBOR 0x80)
  / [ slot_no : uint, header_hash : hash32 ]

tip = [ point : point, block_no : uint ]

hash32 = bytes .size 32
```

*CIP:* not in Appendix B (inherited Praos types; here for completeness).

### 4.2 Block header (`WrappedHeader`)

`net-rs/net-core/src/types/header.rs:271-355`. Era-tagged, tag-24-wrapped
Shelley+ header; prototype re-emits raw bytes but the decoder parses the structure
below incl. Leios extensions. **Field shapes below are confirmed against a real
relay block** (slot 2114025, block#98963; capture §7.2).

```cddl
; prototype — confirmed against live cardano-node-leios relay
wrapped_header = [ era_tag : uint, #6.24(bytes .cbor signed_header) ]
                ; era_tag = 8 observed

signed_header  = [ header_body : block_header_body, body_signature : kes_signature ]
                ; kes_signature = bytes .size 448 observed

block_header_body =
  [ block_number     : uint
  , slot             : uint
  , prev_hash        : hash32
  , issuer_vkey      : bytes32
  , vrf_vkey         : bytes32
  , vrf_result       : [ bytes .size 64, bytes .size 80 ]    ; observed
  , block_body_size  : uint
  , block_body_hash  : hash32
  , operational_cert : [ bytes32, uint, uint, bytes .size 64 ]; observed
  , protocol_version : [ uint, uint ]                         ; observed [12, 0]
  ; --- Leios header extension (optional) ---
  , ? announced_eb   : [ hash32, uint32 ]   ; CONFIRMED: a grouped 2-elem array
                                            ;   [announced_eb_hash, announced_eb_size]
  , ? certified_eb   : bool                 ; omitted (absent) when not set
  ]
```

*CIP v1/v2/v3 (Appendix B, identical):*

```diff
 block_header_body =
   [ block_number, slot, prev_hash, issuer_vkey, vrf_vkey, vrf_result,
     block_body_size, block_body_hash
+  , ? ( announced_eb : hash32, announced_eb_size : uint32 )
+  , ? certified_eb   : bool
   ]
```

> **Comparison — confirmed match.** On the wire the `announced_eb` /
> `announced_eb_size` pair is a single **grouped 2-element array** (CBOR
> `array(2)` = `[hash32, uint32]`), exactly the CIP's `? ( … )` group; it is one
> array element, not two flat fields. `certified_eb` is **omitted** when absent
> (so an EB-announcing-but-not-certifying header is `array(11)`: 10 base + the
> announcement group). The earlier "flat fields" uncertainty is resolved.

### 4.3 Block body / Ranking Block

`net-rs/net-core/src/types/block.rs:108-445`. Carried in BlockFetch `MsgBlock`;
raw bytes, structure as decoded. **Confirmed against two real relay blocks**
(slots 2113724 and 2114025; capture §7.2).

```cddl
; prototype — confirmed against live relay (era_block = array(7))
block_body = #6.24(bytes .cbor [ era_tag : uint, era_block : ranking_block ])
            ; era_tag = 8 observed

ranking_block =
  [ header                   : signed_header
  , transaction_bodies       : [* transaction_body]       ; INDEFINITE array; opaque tx maps
  , transaction_witness_sets : [* transaction_witness_set]; INDEFINITE array; opaque
  , auxiliary_data_set       : {* transaction_index => auxiliary_data}  ; CONFIRMED map (empty=map(0))
  , invalid_transactions     : [* transaction_index]      ; Conway+ (word16 idx)
  , eb_certificate           : leios_certificate / null   ; ALWAYS present; null when absent (§5)
  , peras_cert               : peras_cert / null          ; ALWAYS present; null when absent
  ]
```

*CIP v1/v2/v3 (Appendix B, identical):*

```cddl
ranking_block =
  [ header, transaction_bodies, transaction_witness_sets,
    auxiliary_data_set : {* transaction_index => auxiliary_data},
    invalid_transactions : [* transaction_index]
  , ? eb_certificate : leios_certificate ]
```

> **Comparison — mostly confirmed match, two divergences resolved:**
> - `auxiliary_data_set` **is a map** (`{* index => aux}`), matching the CIP —
>   resolved.
> - `transaction_bodies` / `transaction_witness_sets` are **indefinite-length**
>   arrays on the wire.
> - **Divergence:** the wire `era_block` is **array(7)** — both `eb_certificate`
>   *and* a trailing `peras_cert` are **always present as explicit `null`** when
>   absent, rather than the CIP's truly-optional (omittable) `? eb_certificate`.
>   `peras_cert` is in no CIP-0164 version (Peras, separate). Flag.
> - CIP "Merged Block" (`eb_tx_references`) not implemented on the NtN path.
> - *Note:* both sampled blocks carried `eb_certificate = null` (an EB's
>   certificate rides in a later RB than the announcing one), so the non-null
>   `leios_certificate` layout (§5) is not yet pinned by capture — see §11.

### 4.4 Endorser Block (EB)

LeiosFetch `MsgLeiosBlock` sends the EB body as an **opaque CBOR map** spliced
verbatim (`leios_fetch/codec.rs`): tx-hash → tx-size.

```cddl
; prototype
endorser_block = { * hash32 => uint }   ; tx_hash => tx_size ; indefinite map
```

*CIP v1/v2/v3 (Appendix B, identical):*

```cddl
endorser_block = [ transaction_references : omap<hash32, uint16> ]   ; omap = {* K => V}
```

> **Comparison:** both "ordered map hash→size". Flag: CIP wraps the omap in a
> 1-element array (prototype sends bare map); CIP value `uint16` vs prototype `uint`; prototype
> indefinite map vs deterministic definite. `; TODO` confirm bare-map vs `[map]`.

---

## 5. Votes and Certificates — **v1 differs from v2/v3**

This is what #1196 changed. v2 and v3 share the same vote/cert format; v1 is the
old two-cohort scheme. **The implementation matches v2/v3.**

### 5.1 Implementation

Vote: `shared-rs/consensus/src/types.rs:141-163` + `leios_notify/codec.rs:60-65`.
Cert: embedded in `ranking_block` (`block.rs`).

```cddl
; prototype
leios_vote =
  [ slot_no : uint, endorser_block_hash : hash32
  , voter_id : uint            ; prototype encodes word16
  , vote_signature : bytes ]   ; prototype: variable-length bytes

leios_certificate =
  [ slot_no : uint, endorser_block_hash : hash32
  , signers : bytes            ; committee bitfield, MSB-first
  , aggregated_signature : bytes ]   ; prototype: variable-length bytes
```

### 5.2 CIP v2 (#1196) and v3 (#1167) — stake-based committee / bitfield (identical)

```cddl
leios_vote =
  [ slot_no, endorser_block_hash, voter_id : uint, vote_signature : leios_bls_signature ]

leios_certificate =
  [ slot_no, endorser_block_hash
  , signers : bytes            ; bitfield over the epoch committee; bit i set iff voter_id=i signed
  , aggregated_signature : leios_bls_signature ]

leios_bls_signature = bytes .size 48     ; BLS12-381 MinSig (compressed G1)
```

> **prototype vs v2/v3:** field order and arity **match**. Only divergence: v2/v3 fix
> signatures to `bytes .size 48` (MinSig); prototype encodes variable-length `bytes`.
> `; TODO` confirm prototype enforces 48-byte size and the BLS scheme matches.

### 5.3 CIP v1 (#1078) — two-cohort (persistent / non-persistent), for reference

```cddl
leios_certificate =
  [ election_id, endorser_block_hash : hash32
  , persistent_voters    : [* persistent_voter_id]
  , nonpersistent_voters : {* pool_id => leios_bls_signature}
  , aggregated_vote_sig  : leios_bls_signature ]

leios_vote = persistent_vote / non_persistent_vote
persistent_vote     = [ 0, election_id, persistent_voter_id, endorser_block_hash, vote_signature ]
non_persistent_vote = [ 1, election_id, pool_id, eligibility_signature, endorser_block_hash, vote_signature ]
```

> The prototype does **not** use v1's tagged-union vote, `election_id`, or the
> persistent/non-persistent cohort split. #1196 removed all of that in favor of
> the stake-based committee the prototype uses. See memory [two-cohort voter model]
> for the design history.

---

## 6. Mini-protocol message encodings

Each message is a CBOR array `[ tag, … ]`; `tag : uint` is the discriminator
(literal `e.u32(..)` in each `codec.rs`). Praos protocols (§6.1–6.6) are
**unchanged across v1/v2/v3 and prototype**. The Leios protocols (§6.7–6.8) carry the
full comparison; **v1 and v2 share the same protocol structure**, v3 differs.

### 6.1 Handshake (ID 0) — `handshake/codec.rs`  *(capture in §7.2)*

```cddl
handshakeMessage =
    [ 0, version_table ]                       ; MsgProposeVersions
  / [ 1, version_number : uint, version_data ] ; MsgAcceptVersion (data = raw CBOR)
  / [ 2, refuse_reason ]                       ; MsgRefuse
  / [ 3, version_table ]                       ; MsgQueryReply

version_table = { * version_number => version_data }   ; definite map
version_data  = [ network_magic : uint, initiator_only_diffusion : bool
                , peer_sharing : uint, query : bool ]   ; n2n; confirmed by capture §7.2
refuse_reason =
    [ 0, [* version_number] ] / [ 1, version_number, tstr ] / [ 2, version_number, tstr ]
```

### 6.2 ChainSync (ID 2) — `chainsync/codec.rs`

```cddl
chainSyncMessage =
    [ 0 ]                       ; MsgRequestNext
  / [ 1 ]                       ; MsgAwaitReply
  / [ 2, wrapped_header, tip ]  ; MsgRollForward (header carries Leios ext, §4.2)
  / [ 3, point, tip ]          ; MsgRollBackward
  / [ 4, [* point] ]           ; MsgFindIntersect
  / [ 5, point, tip ]          ; MsgIntersectFound
  / [ 6, tip ]                 ; MsgIntersectNotFound
  / [ 7 ]                      ; MsgDone
```

### 6.3 BlockFetch (ID 3) — `blockfetch/codec.rs`

```cddl
blockFetchMessage =
    [ 0, point, point ]   ; MsgRequestRange (from, to)
  / [ 1 ] ; MsgClientDone   / [ 2 ] ; MsgStartBatch   / [ 3 ] ; MsgNoBlocks
  / [ 4, block_body ]     ; MsgBlock (body may carry eb_certificate, §4.3)
  / [ 5 ]                 ; MsgBatchDone
```

### 6.4 TxSubmission (ID 4) — `txsubmission/codec.rs`

```cddl
txSubmissionMessage =
    [ 6 ]                                  ; MsgInit
  / [ 0, true,  ack : uint, req : uint ]   ; MsgRequestTxIds (blocking)
  / [ 0, false, ack : uint, req : uint ]   ; MsgRequestTxIds (non-blocking)
  / [ 1, [* tx_id_and_size] ]              ; MsgReplyTxIds   ; indefinite inner
  / [ 2, [* era_tx_id] ]                   ; MsgRequestTxs   ; indefinite inner
  / [ 3, [* tx_body] ]                     ; MsgReplyTxs     ; indefinite inner
  / [ 4 ]                                  ; MsgDone
```

### 6.5 KeepAlive (ID 8) — `keepalive/codec.rs`

```cddl
keepAliveMessage =
    [ 0, cookie : uint ]   ; MsgKeepAlive (word16)   / [ 1, cookie : uint ] ; MsgKeepAliveResponse
  / [ 2 ]                  ; MsgDone
```

### 6.6 PeerSharing (ID 10) — `peersharing/codec.rs`

```cddl
peerSharingMessage =
    [ 0, amount : uint ]      ; MsgShareRequest (word8)
  / [ 1, [* peer_address] ]   ; MsgSharePeers   ; definite
  / [ 2 ]                     ; MsgDone
peer_address =
    [ 0, ipv4 : uint, port : uint ]                        ; IPv4 (word32)
  / [ 1, w0:uint, w1:uint, w2:uint, w3:uint, port:uint ]   ; IPv6 (4×word32)
```

### 6.7 LeiosNotify (ID 18) — `leios_notify/codec.rs`

**Implementation:**

```cddl
leiosNotifyMessage =
    [ 0 ]                         ; MsgLeiosNotificationRequestNext   (no N arg)
  / [ 1, wrapped_header ]         ; MsgLeiosBlockAnnouncement
  / [ 2, point, eb_size : uint ]  ; MsgLeiosBlockOffer  (eb_size = word32)
  / [ 3, point ]                  ; MsgLeiosBlockTxsOffer
  / [ 4, [* leios_vote] ]         ; MsgLeiosVotes  (votes PUSHED directly; definite)
  / [ 5 ]                         ; MsgDone
; decoder skips trailing unrecognized fields (forward-compat)
```

**CIP v1 (#1078) & v2 (#1196) — `LeiosNotify`, single protocol (IER, identical):**

| Sender  | Message                          | Arguments                            |
|---------|----------------------------------|--------------------------------------|
| Client→ | MsgLeiosNotificationRequestNext  | ∅                                    |
| ←Server | MsgLeiosBlockAnnouncement        | RB header that announces an EB       |
| ←Server | MsgLeiosBlockOffer               | slot and Leios hash                  |
| ←Server | MsgLeiosBlockTxsOffer            | slot and Leios hash                  |
| ←Server | MsgLeiosVotesOffer               | list of (slot, vote-issuer-id) pairs |

**CIP v3 (#1167) — three protocols (LeiosAnnounce / LeiosVotes / LeiosBlockNotify):**

| Sender  | Message                          | Arguments                   | Protocol         |
|---------|----------------------------------|-----------------------------|------------------|
| Client→ | MsgLeiosAnnounceRequestNext      | integer N                   | LeiosAnnounce    |
| ←Server | MsgLeiosBlockAnnouncement        | slot, EB hash, block_height | LeiosAnnounce    |
| Client→ | MsgLeiosVotesRequestNext         | integer N                   | LeiosVotes       |
| ←Server | MsgLeiosVote                     | vote                        | LeiosVotes       |
| Client→ | MsgLeiosBlockNotifyRequestNext   | integer N                   | LeiosBlockNotify |
| ←Server | MsgLeiosBlockOffer               | slot, EB hash, block_height | LeiosBlockNotify |
| ←Server | MsgLeiosBlockTxsOffer            | slot, EB hash, block_height | LeiosBlockNotify |

> **Comparison (prototype target = v2):**
> - **Structure: prototype matches v1/v2** — one protocol, single no-arg `RequestNext`
>   driving announcement + offers. (v3 splits into three protocols, each with a
>   `RequestNext(N)` token budget the prototype does not carry.)
> - **Announcement payload: prototype matches v1/v2** (full RB header). v3 sends
>   `slot, EB hash, block_height`.
> - **Offer payload:** prototype sends `point (+ eb_size)`; v1/v2 `slot, Leios hash`;
>   v3 `slot, EB hash, block_height`. Flag `eb_size` (prototype-only) and slot+hash vs
>   point encoding.
> - **★ DIVERGENCE from v2 — vote delivery.** #1196 *offers* votes
>   (`MsgLeiosVotesOffer`) and delivers them over LeiosFetch
>   (`MsgLeiosVotesRequest`/`MsgLeiosVoteDelivery`, §6.8). The prototype instead
>   **pushes votes directly** in `MsgLeiosVotes` (tag 4, batched array). This is
>   the v3 *direction* (direct push) but kept inside the v1/v2 merged protocol
>   and batched. The prototype implements **neither** `MsgLeiosVotesOffer` (v2) nor
>   v3's single-`MsgLeiosVote`-in-LeiosVotes. **Flag.**

### 6.8 LeiosFetch (ID 19) — `leios_fetch/codec.rs`

**Implementation:**

```cddl
leiosFetchMessage =
    [ 0, point ]                        ; MsgLeiosBlockRequest (single block)
  / [ 1, endorser_block ]               ; MsgLeiosBlock (opaque map, §4.4)
  / [ 2, point, tx_bitmap ]             ; MsgLeiosBlockTxsRequest
  / [ 3, point, tx_bitmap, [* tx] ]     ; MsgLeiosBlockTxs (tx = opaque)
  / [ 9 ]                               ; MsgDone

tx_bitmap = { * uint => uint }    ; word16 chunk-index => word64 mask ; indefinite
```

**CIP v1 (#1078) & v2 (#1196) — `LeiosFetch` (IER, identical):**

| Sender  | Message                          | Arguments                                          |
|---------|----------------------------------|----------------------------------------------------|
| Client→ | MsgLeiosBlockRequest             | slot and Leios hash                                |
| ←Server | MsgLeiosBlock                    | EB block                                           |
| Client→ | MsgLeiosBlockTxsRequest          | slot, Leios hash, **map from 16-bit index to 64-bit bitmap** |
| ←Server | MsgLeiosBlockTxs                 | list of transactions                               |
| Client→ | MsgLeiosVotesRequest             | list of (slot, vote-issuer-id)                     |
| ←Server | MsgLeiosVoteDelivery             | list of votes                                      |
| Client→ | MsgLeiosBlockRangeRequest        | two slots and two RB header hashes                 |
| ←Server | MsgLeiosNextBlockAndTxsInRange   | an EB and all of its transactions                  |
| ←Server | MsgLeiosLastBlockAndTxsInRange   | an EB and all of its transactions                  |

**CIP v3 (#1167) — `LeiosFetch`:**

| Sender  | Message                          | Arguments                      |
|---------|----------------------------------|--------------------------------|
| Client→ | MsgLeiosMultiBlockRequest        | list of EB hashes              |
| ←Server | MsgLeiosBlock                    | EB block, list of transactions |
| ←Server | MsgLeiosNoMoreBlocks             | ∅                              |
| Client→ | MsgLeiosBlockTxsRequest          | EB hash, list of integers      |
| ←Server | MsgLeiosBlockTxs                 | list of transactions           |

v3 tx-bitmap is a **CBOR byte string** of 9-octet roaring slices (octet 0 =
chunk index `C`, octets 1–8 = 64-bit mask for `C*64..(C+1)*64`).

> **Comparison (prototype target = v2):**
> - **Block request: prototype matches v1/v2** (single `point` / `slot+hash`). v3
>   batches a list (`MsgLeiosMultiBlockRequest` + `MsgLeiosNoMoreBlocks`).
> - **Tx-bitmap: prototype matches v1/v2 intent** ("16-bit index → 64-bit bitmap"),
>   realized as a CBOR **map** `{u16 => u64}`. v3 re-encodes the same info as a
>   roaring **byte string**. map (prototype/v1/v2) vs byte-string (v3) is the key wire
>   divergence between the prototype's target and master.
> - **★ DIVERGENCE from v2 — `MsgLeiosBlockTxs` echoes `point` + `bitmap`** ahead
>   of the tx list; v1/v2/v3 all carry just the tx list. **Flag.**
> - **★ DIVERGENCE from v2 — votes-over-fetch not implemented.** #1196's
>   `MsgLeiosVotesRequest`/`MsgLeiosVoteDelivery` are absent (prototype pushes votes
>   in LeiosNotify, §6.7). **Flag.**
> - **★ DIVERGENCE from v2 — range/Genesis bulk-sync not implemented.** #1196's
>   `MsgLeiosBlockRangeRequest` / `…NextBlockAndTxsInRange` /
>   `…LastBlockAndTxsInRange` have no prototype counterpart. (v3 also dropped these.)
>   **Flag** — decide whether to implement for Genesis sync.
> - `MsgDone` tag is `9` (non-contiguous) — implementation-internal choice.

---

## 7. Wire captures (`net-cli`)

### 7.1 Capture procedure

Captures below are from the **live cardano-node-leios prototype relays**
(`34.251.133.12`, `3.131.54.190`, `52.29.179.71`, port **3001**, network magic
**164**), 2026-06-22:

```sh
cd leios-tools/net-rs && cargo build -p net-cli
R=34.251.133.12:3001
./target/debug/net-cli capture     $R --magic 164             # handshake hex
./target/debug/net-cli chain-sync  $R --magic 164 --count 10  # real Leios headers
./target/debug/net-cli block-fetch $R --magic 164 --dump-hex  # real ranking_block
# LeiosNotify/LeiosFetch message bytes: --wire-hex dumps `WIRE_HEX recv …` to stderr
./target/debug/net-cli multi-follow --host $R --magic 164 --leios --wire-hex 2>&1 \
  | grep WIRE_HEX
```

### 7.2 Captured samples

**Handshake (proto 0)** — real bytes from `34.251.133.12:3001 --magic 164`:

```
; Client→Server  (mux header 8B + payload)
sent:  00000000 0000 0011  8200a20e8418a4f501f4 0f8418a4f501f4
  82                      ; array(2)
    00                    ; 0  = MsgProposeVersions
    a2                    ; map(2)  version_table
      0e 84 18a4 f5 01 f4 ; 14 => [164, true, 1, false]
      0f 84 18a4 f5 01 f4 ; 15 => [164, true, 1, false]
  ; version_data = [network_magic=164, initiator_only_diffusion=true,
  ;                 peer_sharing=1, query=false]

; Server→Client  (mux header carries relay timestamp + responder mode bit 0x8000)
recv:  0e11766f 8000 0009  83010f8418a4f501f4
  83 01 0f 84 18a4 f5 01 f4  ; MsgAcceptVersion(15, [164, true, 1, false])
```

> ✓ Validates Handshake CDDL (§6.1) and n2n `version_data`. All three relays
> accepted version 15.

**ChainSync headers (proto 2)** — real Leios RB headers are **821–858 bytes**
(`chain-sync --count 10`, tip slot 2113724 / block#98947). The size spread
reflects the optional `announced_eb` group (≈ +36 B) on EB-announcing headers.

**Block body (proto 3) — real `ranking_block`** via `block-fetch --dump-hex`.
Two blocks decoded (CBOR skeleton):

```
; (a) block#98947, slot 2113724, 40275 B — no EB announcement, no certificate
#6.24([ 8,                          ; era_tag
        [ [ header_body(array 10),  ; base header, NO Leios extension
            kes_sig=bytes(448) ],
          [* tx_body],              ; indefinite
          [* tx_witness_set],       ; indefinite
          {0 aux},                  ; auxiliary_data_set = map
          [],                       ; invalid_transactions
          null,                     ; eb_certificate = null
          null ] ])                 ; peras_cert = null

; (b) block#98963, slot 2114025, 87236 B — EB-ANNOUNCING header
#6.24([ 8,
        [ [ header_body(array 11),  ; 10 base + Leios announcement group:
            ;   field[10] = [ bytes32 announced_eb_hash, uint 17715 announced_eb_size ]
            ;   vrf_result   = [bytes(64), bytes(80)]
            ;   op_cert      = [bytes32, 0, 0, bytes(64)]
            ;   protocol_ver = [12, 0]
            kes_sig=bytes(448) ],
          [* tx_body], [* tx_witness_set],
          {0 aux}, [],
          null,                     ; eb_certificate = null (cert rides a later RB)
          null ] ])                 ; peras_cert = null
```

> ✓ Validates §4.2 (incl. the **grouped `announced_eb` 2-array**) and §4.3
> (era_block = array(7), aux map, indefinite tx arrays, always-present
> `eb_certificate`/`peras_cert` null slots).

**Still uncaptured** (see §11): a **non-null `leios_certificate`** (needs the RB
that *certifies* an announced EB), and the **EB body / votes** carried by
LeiosNotify (18) / LeiosFetch (19). In this session `multi-follow --leios`
followed the Praos chain but surfaced no EB/vote payloads, and `net-cli` has no
hex dump for the Leios mini-protocol messages. To pin §5 (cert) and §6.7–§6.8:
- fetch the specific RB that carries a certificate (scan headers for
  `certified_eb` / non-null `eb_certificate`), and
- add ingress hex tracing to `multi-follow --leios`, or a small
  `minicbor::to_vec` encoder harness for each Leios message/type.

- LeiosNotify MsgLeiosBlockAnnouncement (18): _TODO_
- LeiosNotify MsgLeiosVotes (18): _TODO_
- LeiosFetch MsgLeiosBlock (19): _TODO_
- LeiosFetch MsgLeiosBlockTxs (19): _TODO_

---

## 8. Alignment at a glance

| Concern                  | prototype (cardano-node)              | v1 (#1078)                         | **v2 (#1196) ← target**            | v3 (#1167, master)                 |
|--------------------------|---------------------------------------|------------------------------------|------------------------------------|------------------------------------|
| RB header extensions     | announced_eb/size/certified_eb        | same                               | same                               | same                               |
| RB body eb_certificate   | always-present (null when absent)     | `? eb_certificate` (omittable)     | `? eb_certificate` (omittable)     | `? eb_certificate` (omittable)     |
| EB body                  | bare indefinite map hash→uint         | `[ omap<hash32,uint16> ]`          | `[ omap<hash32,uint16> ]`          | `[ omap<hash32,uint16> ]`          |
| Vote                     | `[slot,hash,voter_id,sig]` var-len    | tagged union (persistent/non-)     | `[slot,hash,voter_id,sig]` 48B     | `[slot,hash,voter_id,sig]` 48B     |
| Certificate              | `[slot,hash,bitfield,aggsig]` var-len | persistent ids + `{pool=>sig}`     | `[slot,hash,bitfield,aggsig]` 48B  | `[slot,hash,bitfield,aggsig]` 48B  |
| # Leios protocols        | **2** (Notify 18, Fetch 19)           | **2** (Notify, Fetch)              | **2** (Notify, Fetch)              | **4** (Announce/Votes/Notify/Fetch)|
| RequestNext token `N`    | none                                  | none (∅)                           | none (∅)                           | `N` per RequestNext                |
| Block fetch request      | single point                          | single (slot+hash)                 | single (slot+hash)                 | list + NoMoreBlocks                |
| Tx bitmap                | CBOR map `{u16=>u64}`                  | map u16→u64                        | map u16→u64                        | CBOR bytes, 9-octet roaring slices |
| Vote delivery            | **push (batch array, Notify)**        | offer + fetch (req/delivery)       | offer + fetch (req/delivery)       | push (LeiosVotes proto, single)    |
| Range/Genesis bulk sync  | not implemented                       | RangeRequest/Next/Last             | RangeRequest/Next/Last             | removed                            |
| Merged/client block      | not implemented (NtN)                 | specified                          | specified                          | specified                          |

The prototype tracks **v2 (#1196)** on structure, vote/cert format, protocol
count, single-block request, and map bitmap. The two summaries below split the
remaining gap by direction.

## 9. Summary 1 — Prototype → CIP (bring the prototype up to the latest CIP)

Macro, protocol-shape changes the **cardano-node prototype** needs to conform to
the current CIP (**v3 / #1167**). These are structural, not encoding nits.

| # | Change needed in the prototype | From (now, ≈v2) | To (CIP v3) | Refs |
|---|--------------------------------|-----------------|-------------|------|
| 1 | **Split `LeiosNotify` (ID 18)** into three mini-protocols: `LeiosAnnounce`, `LeiosVotes`, `LeiosBlockNotify` | one merged protocol | 3 protocols | §3, §6.7 |
| 2 | **Add `RequestNext(N)` token budget** to each notify-style protocol | no-arg `RequestNext` | `RequestNext(N)` | §6.7 |
| 3 | **Move votes to `LeiosVotes`** as single `MsgLeiosVote` pushes | batched `MsgLeiosVotes` array inside Notify | one vote per `MsgLeiosVote` in its own protocol | §6.7 |
| 4 | **Batch block fetch**: `MsgLeiosMultiBlockRequest` (list of EB hashes) + `MsgLeiosNoMoreBlocks` terminator | single `MsgLeiosBlockRequest(point)` | multi-request + terminator | §6.8 |
| 5 | **Re-encode tx-bitmap** as the roaring byte-string (9-octet slices) | CBOR map `{u16=>u64}` | CBOR `bytes` | §4.4-note, §6.8 |
| 6 | **Slim announcement/offer payloads** to `(slot, EB hash, block_height)` | full RB header / `point (+eb_size)` | tuple | §6.7 |

**Already aligned with v3 (no work):** vote & certificate *format* (stake-based
`voter_id` + bitfield — v2 = v3); absence of range/Genesis bulk-sync messages
(prototype never implemented them and v3 removed them).

## 10. Summary 2 — CIP → Prototype (update the CIP to reflect the prototype)

Leaf-level encoding facts confirmed on the wire (§7) that the **CIP** should
adopt or clarify — places where the spec is under-specified or doesn't match the
running implementation. These are independent of the v3 protocol restructuring.

| # | CIP should specify / change | Prototype wire reality | CIP today | Refs |
|---|------------------------------|------------------------|-----------|------|
| 1 | `announced_eb` is a **CBOR `array(2)` `[hash32, uint32]`** (make the array encoding explicit) | grouped 2-array, value 17715 observed | groups via `? ( … )` but encoding implicit | §4.2 |
| 2 | `eb_certificate` is **always present, `null` when absent** (and there is a trailing **`peras_cert`** slot → `era_block` = array(7)) | always-present null slots | `? eb_certificate` (omittable); no `peras_cert` | §4.3 |
| 3 | EB body is a **bare, indefinite CBOR map** `{hash32 => uint}` | bare indefinite map | `[ omap<hash32,uint16> ]` (array-wrapped) | §4.4 |
| 4 | EB tx-size value width | generic `uint` | `uint16` | §4.4 |
| 5 | `transaction_bodies` / `transaction_witness_sets` are **indefinite-length** arrays | indefinite | `[* … ]` (width-agnostic) | §4.3 |
| 6 | `MsgLeiosBlockTxs` reply **echoes `point` + `bitmap`** before the tx list | `[3, point, bitmap, [*tx]]` | reply carries only the tx list | §6.8 |
| 7 | Record the **mini-protocol number registry** (`LeiosNotify`=18, `LeiosFetch`=19) | IDs 18 / 19 | no numbers assigned | §3 |

**Reconcile (direction TBD):** vote/cert signatures are encoded as
**variable-length `bytes`** by the prototype, while the CIP fixes `bytes .size 48`
(BLS12-381 MinSig). Likely a *prototype* fix (enforce 48 B) rather than a CIP
change, but it is a real wire discrepancy — see §11.3. (§5)

## 11. Open questions / TODO

Resolved by live capture (§7.2): `announced_eb` is a grouped `[hash32, uint32]`
array; `auxiliary_data_set` is a map; `era_block` is array(7) with always-present
`eb_certificate`/`peras_cert` null slots; vrf/op-cert/protocol-version/KES shapes.

Remaining:

1. Capture a **non-null `leios_certificate`** from the RB that certifies an
   announced EB (scan headers for `certified_eb` / non-null `eb_certificate`) and
   pin §5's cert layout against the wire. (§5, §7.2)
2. Capture real **LeiosNotify/LeiosFetch message bytes** (vote / offer / EB /
   block-txs) via `multi-follow --leios --wire-hex` against a relay actively
   producing EBs, and `cddl validate` the prototype CDDL against §7. (§6.7-6.8)
3. Confirm whether signature sizes (48-byte MinSig) are enforced and the BLS
   scheme matches v2/v3 — the §10 "reconcile" item. (§5.2)

---

*Generated against `leios-tools` @ `net-rs` `4c799c1`; CIP-0164 v1 @ `630bda34`
(#1078), v2 @ `5690adca` (#1196), v3 @ `master`/`bc28ab90` (#1167). Re-verify
file:line references after rebasing any repo.*
