# Leios Block and Protocol Encoding — Prototype vs CIP-0164

> Reference for the **cardano-node Leios prototype**'s on-the-wire (CBOR) block
> formats and node-to-node mini-protocol messages, expressed as CDDL, with a
> two-way comparison to CIP-0164 "Ouroboros Linear Leios".

The prototype implements an **earlier revision** of CIP-0164's Leios networking
than the current published CIP (see the revision history below), so the two have
diverged. This document:

- gives the prototype's actual wire format (§3–§7), validated against the
  authoritative Haskell source **and** live relay captures;
- **§9 — Prototype → CIP:** what the prototype must change to converge on the
  current CIP (protocol-shape work);
- **§10 — CIP → Prototype:** leaf-level encoding the CIP should adopt to match
  the running prototype.

**`net-node` reflects the prototype.** The Rust stack in
[`leios-tools`](https://github.com/cardano-scaling/leios-tools) (`net-rs/net-core`) is a faithful
reimplementation of the prototype's wire format; its `minicbor`
encoders/decoders are used here as the legible source of the CDDL. Where this
doc says "the prototype", that is the cardano-node implementation as observed on
the wire and mirrored by `net-node`.

## Where the prototype sits — CIP-0164 revision history

CIP-0164's Leios networking changed across three merged PRs. **The prototype
implements the middle revision (#1196)** — that is the baseline for the
prototype → CIP gap in §9.

| PR | Merge | Date | What it changed |
|----|-------|------|------------------|
| [#1078][pr1078] | `630bda34` | 2026-01-06 | First published Leios CIP. **2 Leios mini-protocols** (LeiosNotify + LeiosFetch); **two-cohort** votes & certs (persistent / non-persistent); `{u16=>u64}` map tx-bitmap; vote delivery via offer→request; range/Genesis bulk-sync messages. |
| [#1196][pr1196] | `5690adca` | 2026-05-27 | "Replace wFA^LS committee with **stake-based committee selection**." Keeps #1078's protocol structure, map bitmap and vote-delivery; **replaces votes & certs** with a uniform `voter_id`-indexed vote + bitfield certificate. **← the prototype tracks this.** |
| [#1167][pr1167] | `bc28ab90` | 2026-06-09 | "Refine Leios protocols." **Splits LeiosNotify into 3 protocols**; **direct single-vote push**; **roaring byte-string** tx-bitmap; `RequestNext(N)` token budget; **drops** range/Genesis messages. Votes & certs unchanged from #1196. **Current `master`** — the "CIP-0164 (current)" column throughout this doc. |

So the prototype = #1196's design: two protocols, no-arg `RequestNext`,
single-block fetch, map tx-bitmap, and #1196's `voter_id` vote (the certificate
from #1196 is specified but the prototype only mocks it, §5.1) — **with one
deliberate departure: it sends votes *directly* via `MsgLeiosVotes` in LeiosNotify
rather than #1196's offer→fetch loop** (`MsgLeiosVotesOffer`, then
`MsgLeiosVotesRequest` / `MsgLeiosVoteDelivery` over LeiosFetch). That direct push
anticipates #1167's direction, though #1167 puts it in a dedicated LeiosVotes
protocol (§6.7). The current CIP (#1167) moved ahead on the rest of the protocol
shape; §9 is that delta.

[pr1078]: https://github.com/cardano-foundation/CIPs/pull/1078
[pr1196]: https://github.com/cardano-foundation/CIPs/pull/1196
[pr1167]: https://github.com/cardano-foundation/CIPs/pull/1167
[cb68]: https://github.com/cardano-scaling/cardano-blueprint/issues/68

## 1. Scope and sources

- **Implementation tracked:** the **cardano-node Leios prototype** (prototype
  testnet relays). Its wire format is read from `net-node`
  (`leios-tools/net-rs/net-core`, CBOR via `minicbor` v0.25) and confirmed
  against live captures (§7). Standard CBOR (RFC 8949); no custom tags beyond
  `#6.24` (CBOR-in-CBOR).
- **Authoritative Haskell source (validated against):** the prototype's Leios
  network code is in **ouroboros-consensus** at the commit cardano-node's
  `leios-prototype` branch pins —
  [`e3803b0c`](https://github.com/IntersectMBO/ouroboros-consensus/tree/e3803b0c86fc0b5f0a7b8f3a977aebf5afe31b8b/ouroboros-consensus/src/ouroboros-consensus)
  — specifically `LeiosDemoOnlyTestNotify.hs` (proto 18),
  `LeiosDemoOnlyTestFetch.hs` (proto 19) and `LeiosDemoTypes.hs` (vote / point /
  EB / announcement / certificate types).
  It is **not** in `ouroboros-network` (whose pinned commit `ff3e39af` has no
  Leios protocols; that repo's `ObjectDiffusion` protocol is for **Peras**, not
  Leios). §4.1, §4.2, §4.4, §5.1, §6.7 and §6.8 are confirmed against this source
  (`✓` markers inline) and match the live captures (§7).
- **Reference spec:** [CIP-0164](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0164),
  Appendix B "Wire Format Specifications (CDDL)" and §"Leios Mini-Protocols" /
  IER table (current published version).
- **Out of scope:** the node-to-client (N2C) path — including the merged/client
  block (§4.3), which the prototype node implements but net-node (N2N-only) does
  not use; and Praos-internal ledger structures (tx bodies, witness sets,
  non-Leios certs), carried as opaque CBOR and not reparsed.

## 2. Conventions

- `bytesN` = `bytes .size N`; `hash32` = `bytes .size 32`.
- `#6.24(X)` = CBOR byte string tagged 24 wrapping the CBOR of `X` (RFC 8949
  §3.4.5.1).
- Arrays/maps are **definite-length** unless annotated `; indefinite`.
- Raw pass-through fields: CDDL gives logical shape; body notes "raw".
- Era tagging: NtN txs/tx-ids carry a leading HFC era index (`word16`); §6.4.

## 3. Mini-protocol catalogue

Protocol IDs are the mux `ProtocolId` (`u16`). The Praos protocols are inherited
unchanged; the two Leios protocols are the prototype's own.

| ID | Protocol      | Source (`net-core`)   | CIP-0164 (current)                            |
|----|---------------|-----------------------|-----------------------------------------------|
| 0  | Handshake     | `handshake/mod.rs`    | Praos, unchanged                              |
| 2  | ChainSync     | `chainsync/mod.rs`    | Praos, unchanged                              |
| 3  | BlockFetch    | `blockfetch/mod.rs`   | Praos, unchanged                              |
| 4  | TxSubmission  | `txsubmission/mod.rs` | Praos, unchanged                              |
| 8  | KeepAlive     | `keepalive/mod.rs`    | Praos, unchanged                              |
| 10 | PeerSharing   | `peersharing/mod.rs`  | Praos, unchanged                              |
| 18 | LeiosNotify   | `leios_notify/mod.rs` | split into LeiosAnnounce + LeiosVotes + LeiosBlockNotify |
| 19 | LeiosFetch    | `leios_fetch/mod.rs`  | LeiosFetch                                    |

> Protocol IDs **18/19 are fixed by the prototype's Haskell source** —
> `leiosNotifyMiniProtocolNum = 18` and `leiosFetchMiniProtocolNum = 19` in
> ouroboros-consensus `LeiosDemoOnlyTest{Notify,Fetch}.hs` (@ `e3803b0c`). The
> CIP assigns no numbers. The prototype runs **two** Leios protocols; the current
> CIP splits the notify side into **three** (§9).

---

## 4. Block and data-structure encodings

> The Ranking Block, block header (incl. Leios extensions) and Endorser Block
> CDDL are unchanged across CIP revisions; the CIP column shows the current
> Appendix B.

### 4.1 Point and Tip

`shared-rs/consensus/src/types.rs`

```cddl
point =
    []                          ; origin (CBOR 0x80)
  / [ slot_no : uint, header_hash : hash32 ]

tip = [ point : point, block_no : uint ]
```

*CIP:* not in Appendix B (inherited Praos types; here for completeness).

### 4.2 Block header (`WrappedHeader`)

`net-rs/net-core/src/types/header.rs`. Era-tagged, tag-24-wrapped Shelley+
header; the prototype re-emits raw bytes but the decoder parses the structure
below incl. Leios extensions. **Field shapes confirmed against a real relay
block** (slot 2114025, block#98963; §7.2).

```cddl
; prototype — confirmed against live relay
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
  , ? announced_eb   : [ hash32, uint32 ]   ; ONE nested array(2) element
                                            ;   [announced_eb_hash, announced_eb_size]
  , ? certified_eb   : bool                 ; omitted (absent) when not set
  ]
```

*CIP (Appendix B):*

```diff
 block_header_body =
   [ block_number, slot, prev_hash, issuer_vkey, vrf_vkey, vrf_result,
     block_body_size, block_body_hash
+  , ? ( announced_eb : hash32, announced_eb_size : uint32 )
+  , ? certified_eb   : bool
   ]
```

> **Divergence (CDDL semantics).** On the wire the announcement is **one nested
> `array(2)`** = `[announced_eb_hash, announced_eb_size]` — a single header_body
> element (an EB-announcing-but-not-certifying header is therefore `array(11)`:
> 10 base + 1 element). Confirmed by the capture (§7.2, field[10] = `array(2)`)
> and by `EbAnnouncement`'s `encodeListLen 2` in the source. The CIP's
> `? ( announced_eb : hash32, announced_eb_size : uint32 )` is a **transparent
> CDDL group**: `( … )` inlines its members as **two flat array entries**, so the
> CIP would put `announced_eb` and `announced_eb_size` as separate fields (an
> announcing header would be `array(12)`). Nested array (wire) vs flat pair (CIP)
> differ — the CIP should make it an explicit nested array to match (§10).
>
> **Decoding `array(11)` requires type-checking, not position.** Both
> `announced_eb` and `certified_eb` are optional and trailing, so a header_body
> with exactly one extra field (`array(11)`) is ambiguous by arity alone — the
> single extra element is either `announced_eb` (a CBOR **array**) or
> `certified_eb` (a CBOR **bool**). A decoder must inspect the element's CBOR
> type to tell which is present: `array(2)` ⇒ `announced_eb`, `bool` ⇒
> `certified_eb`. (In this nested encoding `array(10)` ⇒ neither and `array(12)` ⇒
> both — announcement element then bool.) net-node decodes them by exactly this
> dispatch.
>
> The **original CIP design** avoided this *via the length alone* — no
> type-checking. With the flat transparent group, `announced_eb` contributes
> **two** elements (`hash32`, `uint32`) and `certified_eb` **one** (`bool`), so
> the four presence combinations map to four distinct lengths: `array(10)` ⇒
> neither, `array(11)` ⇒ `certified_eb` only, `array(12)` ⇒ `announced_eb` only,
> `array(13)` ⇒ both. The length is the discriminator. The prototype's nested
> `array(2)` collapses `announced_eb` to a single element, making `array(11)`
> ambiguous and forcing the type dispatch above. (This is a concrete cost of the
> nested-vs-flat divergence, not just a notational one.)

### 4.3 Block body / Ranking Block

`net-rs/net-core/src/types/block.rs`. Carried in BlockFetch `MsgBlock`; raw
bytes, structure as decoded. **Confirmed against two real relay blocks** (slots
2113724 and 2114025; §7.2).

```cddl
; prototype — confirmed against live relay (era_block = array(7))
block_body = #6.24(bytes .cbor [ era_tag : uint, era_block : ranking_block ])
            ; era_tag = 8 observed

ranking_block =
  [ header                   : signed_header
  , transaction_bodies       : [* transaction_body]       ; INDEFINITE array; opaque tx maps
  , transaction_witness_sets : [* transaction_witness_set]; INDEFINITE array; opaque
  , auxiliary_data_set       : {* transaction_index => auxiliary_data}  ; map (empty = map(0))
  , invalid_transactions     : [* transaction_index]      ; Conway+ (word16 idx)
  , eb_certificate           : array(0) / null   ; ALWAYS present; mock placeholder (§5.1)
  , peras_cert               : peras_cert / null  ; ALWAYS present; null when absent
  ]
  ; NOTE: eb_certificate is a MOCK — array(0) placeholder or null, NOT a
  ;       leios_certificate (§5.1). Observed null in both captured RBs.
```

*CIP (Appendix B):*

```cddl
ranking_block =
  [ header, transaction_bodies, transaction_witness_sets,
    auxiliary_data_set : {* transaction_index => auxiliary_data},
    invalid_transactions : [* transaction_index]
  , ? eb_certificate : leios_certificate ]
```

> **Comparison:**
> - `auxiliary_data_set` is a **map** (matches the CIP);
>   `transaction_bodies` / `transaction_witness_sets` are **indefinite-length**.
> - The wire `era_block` is **array(7)** — both `eb_certificate` *and* a trailing
>   `peras_cert` are **always present** (`null` when absent), rather than the
>   CIP's omittable `? eb_certificate`. `peras_cert` is in no CIP-0164 version
>   (Peras, separate).
> - **`eb_certificate` is a mock, not implemented** — `array(0)` placeholder
>   (certifying block) or `null` (absent), not a `leios_certificate` (§5.1). Both
>   sampled blocks carried `null`.
> - The CIP "Merged Block" (`eb_tx_references`) is a **node-to-client (N2C)**
>   structure — the prototype node implements it for local clients, but it does
>   not appear on the **node-to-node (N2N)** path this doc covers, and net-node
>   (N2N-only) does not use it. Out of scope here.

### 4.4 Endorser Block (EB)

LeiosFetch `MsgLeiosBlock` carries the EB body. net-node relays it as opaque
CBOR; the **authoritative encoding is `encodeLeiosEb`** in ouroboros-consensus
`LeiosDemoTypes.hs` (@ `e3803b0c`). It is purely `(tx_hash, tx_size)` pairs —
**no per-tx validity bits** (validity is tracked at the RB level via
`invalid_transactions`, §4.3).

```cddl
; prototype — per encodeLeiosEb; WIRE-CONFIRMED (§7.2 MsgLeiosBlock, map(639))
endorser_block = { * hash32 => uint32 }   ; tx_hash => tx_size ; DEFINITE map (encodeMapLen)
```

*CIP (Appendix B):*

```cddl
endorser_block = [ transaction_references : omap<hash32, uint16> ]   ; omap = {* K => V}
```

> **Comparison.** The prototype sends a **bare, definite-length CBOR map**
> `{hash32 => uint32}` — *not* array-wrapped, *not* indefinite, with **uint32**
> sizes. The CIP array-wraps the omap and types the size `uint16`. Divergences
> for the CIP: drop the 1-element array wrapper and widen the size to `uint32`.
> (The LeiosFetch **tx-bitmap** *is* an indefinite map, §6.8 — only the EB body
> is definite.)

---

## 5. Votes and Certificates

The prototype's **vote** is confirmed on the wire and matches the CIP. The
prototype's **certificate is not yet implemented** (§5.1) — it is a mock, emitted
as an `array(0)` placeholder (or `null` when absent), so the CIP certificate
structure is a target, not current reality.

### 5.1 Prototype

Vote: `shared-rs/consensus/src/types.rs` + `leios_notify/codec.rs`. Certificate:
embedded in `ranking_block` (`block.rs`).

```cddl
; prototype — vote CONFIRMED on the wire (§7.2 MsgLeiosVotes capture)
;            and against encodeLeiosVote (LeiosDemoTypes.hs @ e3803b0c)
leios_vote =
  [ slot_no : uint, endorser_block_hash : hash32
  , voter_id : uint            ; word16; small committee index (0,1,2 observed)
  , vote_signature : bytes .size 48 ]   ; BLS12-381 MinSig (minSigPoP DSIGN)

; CERTIFICATE IS NOT IMPLEMENTED. LeiosDemoTypes.hs @ e3803b0c:
;   newtype LeiosCertificate = LeiosCertificate { leiosCertificateEbPoint :: LeiosPoint }
;   -- FIXME(bladyjoker): Mocked  (no bitfield, no aggregated_signature, no CBOR instance)
; On the wire the eb_certificate slot is a placeholder, NOT a leios_certificate:
eb_certificate_wire =
    array(0)     ; empty-array placeholder when a block "certifies" (mock)
  / null         ; absent — observed in every captured (non-certifying) RB
```

### 5.2 CIP — stake-based committee / bitfield certificate

```cddl
leios_vote =
  [ slot_no, endorser_block_hash, voter_id : uint, vote_signature : leios_bls_signature ]

leios_certificate =
  [ slot_no, endorser_block_hash
  , signers : bytes            ; bitfield over the epoch committee; bit i set iff voter_id=i signed
  , aggregated_signature : leios_bls_signature ]

leios_bls_signature = bytes .size 48     ; BLS12-381 MinSig (compressed G1)
```

> **Vote: match (confirmed).** Field order and arity agree, and the live
> `MsgLeiosVotes` capture (§7.2) shows the **vote signature is exactly 48 bytes**,
> matching the CIP's `bytes .size 48` MinSig.
> **Certificate: prototype gap.** The CIP structure is correct; the prototype
> emits only the mock placeholder. Implementing the real bitfield + aggregated
> signature is a prototype → CIP task (§9).

---

## 6. Mini-protocol message encodings

Each message is a CBOR array `[ tag, … ]`; `tag : uint` is the discriminator.
Praos protocols (§6.1–6.6) are inherited unchanged. The Leios protocols
(§6.7–6.8) carry the prototype-vs-CIP comparison.

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

**Prototype:**

```cddl
; ✓ validated against ouroboros-consensus LeiosDemoOnlyTestNotify.hs @ e3803b0c
leiosNotifyMessage =
    [ 0 ]                         ; MsgLeiosNotificationRequestNext   (no N arg)
  / [ 1, wrapped_header ]         ; MsgLeiosBlockAnnouncement
  / [ 2, point, eb_size : uint ]  ; MsgLeiosBlockOffer  (eb_size = word32)   ✓ live §7.2
  / [ 3, point ]                  ; MsgLeiosBlockTxsOffer                     ✓ live §7.2
  / [ 4, [* leios_vote] ]         ; MsgLeiosVotes  (pushed directly; definite) ✓ live §7.2
  / [ 5 ]                         ; MsgDone
; decoder skips trailing unrecognized fields (forward-compat)
; ✓ = exact encoding confirmed against live relay capture (§7.2);
;     MsgLeiosBlockAnnouncement (tag 1) not captured in-window.
```

**CIP — three protocols (LeiosAnnounce / LeiosVotes / LeiosBlockNotify):**

| Sender  | Message                          | Arguments                   | Protocol         |
|---------|----------------------------------|-----------------------------|------------------|
| Client→ | MsgLeiosAnnounceRequestNext      | integer N                   | LeiosAnnounce    |
| ←Server | MsgLeiosBlockAnnouncement        | slot, EB hash, block_height | LeiosAnnounce    |
| Client→ | MsgLeiosVotesRequestNext         | integer N                   | LeiosVotes       |
| ←Server | MsgLeiosVote                     | vote                        | LeiosVotes       |
| Client→ | MsgLeiosBlockNotifyRequestNext   | integer N                   | LeiosBlockNotify |
| ←Server | MsgLeiosBlockOffer               | slot, EB hash, block_height | LeiosBlockNotify |
| ←Server | MsgLeiosBlockTxsOffer            | slot, EB hash, block_height | LeiosBlockNotify |

> **Divergences from the CIP:**
> - **One merged protocol vs three.** The prototype drives announcement + offers
>   + votes from a single `LeiosNotify` with one no-arg `RequestNext`; the CIP
>   splits these into three protocols, each with a `RequestNext(N)` **token
>   budget** the prototype does not carry.
> - **Announcement payload:** the prototype sends the **full RB header**; the CIP
>   sends `slot, EB hash, block_height`.
> - **Offer payload:** the prototype sends `point (+ eb_size)`; the CIP sends
>   `slot, EB hash, block_height`.
> - **Vote delivery:** the prototype **pushes votes directly** in `MsgLeiosVotes`
>   (tag 4, batched array). The CIP pushes a single `MsgLeiosVote` per message in
>   a dedicated LeiosVotes protocol.

### 6.8 LeiosFetch (ID 19) — `leios_fetch/codec.rs`

**Prototype:**

```cddl
; ✓ validated against ouroboros-consensus LeiosDemoOnlyTestFetch.hs @ e3803b0c
leiosFetchMessage =
    [ 0, point ]                        ; MsgLeiosBlockRequest (single block)
  / [ 1, endorser_block ]               ; MsgLeiosBlock (§4.4)         ✓ live §7.2
  / [ 2, point, tx_bitmap ]             ; MsgLeiosBlockTxsRequest
  / [ 3, point, tx_bitmap, [* tx] ]     ; MsgLeiosBlockTxs (echoes point+bitmap; tx = bytes)  ✓ live §7.2
  / [ 9 ]                               ; MsgDone (note: word 9)

tx_bitmap = { * uint => uint }    ; word16 chunk-index => word64 mask ; INDEFINITE (encodeMapLenIndef)  ✓ live §7.2
```

**CIP — `LeiosFetch`:**

| Sender  | Message                          | Arguments                      |
|---------|----------------------------------|--------------------------------|
| Client→ | MsgLeiosMultiBlockRequest        | list of EB hashes              |
| ←Server | MsgLeiosBlock                    | EB block, list of transactions |
| ←Server | MsgLeiosNoMoreBlocks             | ∅                              |
| Client→ | MsgLeiosBlockTxsRequest          | EB hash, list of integers      |
| ←Server | MsgLeiosBlockTxs                 | list of transactions           |

The CIP tx-bitmap is a **CBOR byte string** of 9-octet roaring slices (octet 0 =
chunk index `C`, octets 1–8 = 64-bit mask for `C*64..(C+1)*64`).

> **Divergences from the CIP:**
> - **Block request:** the prototype takes a single `point`; the CIP batches a
>   list (`MsgLeiosMultiBlockRequest` + a `MsgLeiosNoMoreBlocks` terminator).
> - **Tx-bitmap:** the prototype uses a CBOR **map** `{u16 => u64}`; the CIP uses
>   the roaring **byte string**. Same information, incompatible encoding — the key
>   wire divergence.
> - **`MsgLeiosBlockTxs` echoes `point` + `bitmap`** ahead of the tx list; the
>   CIP reply carries just the tx list.
> - `MsgDone` tag is `9` (non-contiguous).

> **EB `point` encoding (spec vs wire) — [cardano-blueprint#68][cb68].** The EB
> point is specified in the CDDL as a **transparent group** `(slot, eb_hash)`
> (inlines as **two flat fields**) but encoded on the wire as a **nested
> `array(2)`** (`encodeLeiosPoint` = `encodeListLen 2` in `LeiosDemoTypes.hs`,
> confirmed by the offer captures, §7.2) — the **same group-vs-nested-array
> mismatch** as `announced_eb` (§4.2). It matters in LeiosFetch because the client
> *sends* the point in `MsgLeiosBlockRequest`: a client that follows the CDDL
> literally (flat) and a peer that uses the wire (nested) would **fail the decode
> and reset** the protocol. **net-node uses the array encoding** (`Point::Specific`
> → `e.array(2)`), matching the wire — and we have **confirmed this interoperates
> against the live relays**: the `MsgLeiosBlock` and `MsgLeiosBlockTxs` fetches
> (§7.2) succeeded with no reset, with net-node sending the array-encoded `point`.
> So the wire is the nested array and the implementations agree; only the
> CDDL/spec still needs fixing to match (§10 row 8, [cardano-blueprint#68][cb68]).

---

## 7. Wire captures (`net-cli`)

### 7.1 Capture procedure

Captures are from the **live cardano-node-leios prototype relays**
(`34.251.133.12`, `3.131.54.190`, `52.29.179.71`, port **3001**, network magic
**164**), 2026-06-22:

```sh
cd leios-tools/net-rs && cargo build -p net-cli
R=34.251.133.12:3001
./target/debug/net-cli capture     $R --magic 164             # handshake hex
./target/debug/net-cli chain-sync  $R --magic 164 --count 10  # real Leios headers
./target/debug/net-cli block-fetch $R --magic 164 --dump-hex  # real ranking_block
# Leios message bytes: --wire-hex dumps `WIRE_HEX recv …` to stderr.
#   --fetch-eb / --fetch-eb-txs actively request the EB body / its txs on each
#   offer, so the LeiosFetch replies (MsgLeiosBlock / MsgLeiosBlockTxs) are captured.
./target/debug/net-cli multi-follow --host $R --magic 164 --leios \
  --wire-hex --fetch-eb --fetch-eb-txs 2>&1 | grep WIRE_HEX
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

> ✓ Validates the Handshake CDDL (§6.1) and n2n `version_data`. All three relays
> accepted version 15.

**ChainSync headers (proto 2)** — real Leios RB headers are **821–858 bytes**
(`chain-sync --count 10`, tip slot 2113724 / block#98947). The size spread
reflects the optional `announced_eb` array (≈ +36 B) on EB-announcing headers.

**Block body (proto 3) — real `ranking_block`** via `block-fetch --dump-hex`.
Two blocks decoded (CBOR skeleton):

```
; (a) block#98947, slot 2113724, 40275 B — plain RB (no EB announcement)
#6.24([ 8,                          ; era_tag
        [ [ header_body(array 10),  ; base header, no Leios extension
            kes_sig = bytes(448) ],
          [* tx_body],              ; indefinite
          [* tx_witness_set],       ; indefinite
          {0 aux},                  ; auxiliary_data_set = map (empty here)
          [],                       ; invalid_transactions
          null,                     ; eb_certificate (absent)
          null ] ])                 ; peras_cert (absent)

; (b) block#98963, slot 2114025, 87236 B — EB-announcing RB
#6.24([ 8,                          ; era_tag
        [ [ header_body(array 11),  ; 10 base fields (…, §4.2) + 1 announcement element:
            ;   field[10] = array(2) [ bytes32 announced_eb_hash, uint 17715 announced_eb_size ]
            kes_sig = bytes(448) ],
          [* tx_body],              ; indefinite
          [* tx_witness_set],       ; indefinite
          {0 aux},                  ; auxiliary_data_set = map (empty here)
          [],                       ; invalid_transactions
          null,                     ; eb_certificate (absent; mock array(0) only in a certifying RB, §5.1)
          null ] ])                 ; peras_cert (absent)
```

> ✓ Validates §4.2 (incl. the **nested `announced_eb` `array(2)`**) and §4.3
> (era_block = array(7), aux map, indefinite tx arrays, always-present
> `eb_certificate`/`peras_cert` slots — both `null` here).

**LeiosNotify messages (proto 18)** — real bytes captured via
`multi-follow --leios --wire-hex` against `34.251.133.12:3001`, slot ~2118596:

```
; MsgLeiosBlockOffer  (45 B)
8302821a002053c45820 b073ce6d…07555 194533
  83 02                       ; array(3), 2 = MsgLeiosBlockOffer
     82 1a 002053c4 5820 b073…07555   ; point = [slot 2118596, eb_hash(32)]
     19 4533                  ; eb_size = 17715 (word32)

; MsgLeiosBlockTxsOffer  (42 B)
8203821a002053c45820 b073ce6d…07555
  82 03                       ; array(2), 3 = MsgLeiosBlockTxsOffer
     82 1a 002053c4 5820 b073…07555   ; point = [slot 2118596, eb_hash(32)]

; MsgLeiosVotes  (94 B) — one vote
820481 841a002053c45820 b073ce6d…07555 00 5830 ab067bad…0d88f
  82 04                       ; array(2), 4 = MsgLeiosVotes
     81                       ; array(1) — vote list (definite)
        84                    ; array(4) vote
           1a 002053c4        ; slot_no 2118596
           5820 b073…07555    ; endorser_block_hash(32)
           00                 ; voter_id 0   (observed 0,1,2 — small committee index)
           5830 ab06…0d88f    ; vote_signature = bytes(48)  ← BLS MinSig
```

> ✓ Validates §6.7 (`MsgLeiosBlockOffer` = `[2, point, eb_size]`,
> `MsgLeiosBlockTxsOffer` = `[3, point]`, `MsgLeiosVotes` = `[4, [* vote]]`),
> §4.1 (`point` = `[slot, hash32]`), and §5.1 — **vote signatures are exactly 48
> bytes** (fixed 48-B MinSig). The `eb_size` in an offer matches the
> `announced_eb_size` carried in the RB header (§4.2).

**LeiosFetch `MsgLeiosBlock` — the EB body (proto 19)** — real bytes captured via
`multi-follow --leios --wire-hex --fetch-eb` (the `--fetch-eb` flag issues a
`MsgLeiosBlockRequest` on each offer), EB at slot 2132960, **23009 B**:

```
8201 b9027f 5820 d33cb51a…15cb2d 18c8 5820 ebf15364…03f21cc 18c8 …
  82 01                       ; array(2), 1 = MsgLeiosBlock
     b9 027f                  ; map(639)  ← DEFINITE (0xb9 = map, 2-byte length 0x027f)
        5820 d33cb5…15cb2d    ; tx_hash (32 B)
        18 c8                 ; tx_size = 200   (canonical uint; type is uint32)
        5820 ebf153…03f21cc   ; tx_hash (32 B)
        18 c8                 ; tx_size = 200
        … 639 entries total, all keys bytes(32), values uint; 0 trailing bytes
```

> ✓ Validates §6.8 (`MsgLeiosBlock` = `[1, endorser_block]`) and §4.4 — the EB
> body is a **definite** CBOR map (`map(639)`) of `hash32 => uint`, confirming on
> the wire what was read from `encodeLeiosEb`. (Sizes are 200 here — uniform
> synthetic txs — encoded as canonical minimal uint, e.g. `18c8`.) net-node's
> `point` request encoding interoperated with the relay (no reset), per §6.8.

**LeiosFetch `MsgLeiosBlockTxs` — the transaction fetch (proto 19)** — real bytes
captured via `--fetch-eb-txs` (issues a `MsgLeiosBlockTxsRequest` with bitmap
`{0: 0xff..ff}` = tx indices 0–63 on each txs-offer), EB at slot 2133539,
**5510 B**, 27 txs:

```
8403 821a00208e23 5820 13d48978…a8f5ce7 bf 00 1b ffffffffffffffff ff 981b 5820… …
  84 03                       ; array(4), 3 = MsgLeiosBlockTxs
     82 1a00208e23 5820 …     ; point = [slot 2133539, eb_hash(32)]   (ECHOED)
     bf 00 1b ffffffffffffffff ff   ; bitmap = INDEFINITE map { 0 => 0xffffffffffffffff } (ECHOED)
     98 1b                    ; array(27)  ← DEFINITE tx_list
        5820 …                ; tx (opaque bytes; 200 B each here)
        … 27 txs, total 5400 tx bytes; 0 trailing bytes
```

> ✓ Validates §6.8 `MsgLeiosBlockTxs` = `[3, point, tx_bitmap, [* tx]]`: the reply
> **echoes the `point` and the `tx_bitmap`**, the bitmap is an **indefinite** map,
> and the tx list is a **definite** array of opaque tx bytes.

**Not yet wire-captured:**
- `MsgLeiosBlockAnnouncement` (proto 18, tag 1 — the RB header): not pushed in
  the capture window. Its payload type (the `announcement` codec parameter,
  decoded as `wrapped_header`) is unconfirmed on the wire.

---

## 8. Prototype vs CIP — at a glance

| Concern                  | prototype (cardano-node)                | CIP-0164 (current)                 |
|--------------------------|-----------------------------------------|------------------------------------|
| RB header extensions     | announced_eb / size / certified_eb      | same                               |
| RB body eb_certificate   | **mock**: array(0)/null, always-present | `? eb_certificate` (omittable)     |
| EB body                  | bare **definite** map hash→uint32       | `[ omap<hash32, uint16> ]`         |
| Vote                     | `[slot, hash, voter_id, sig48]`         | `[slot, hash, voter_id, sig48]`    |
| Certificate              | **not implemented** (mock array(0))     | `[slot, hash, bitfield, aggsig]` 48B |
| # Leios protocols        | **2** (Notify 18, Fetch 19)             | **4** (Announce / Votes / Notify / Fetch) |
| RequestNext token `N`    | none                                    | `N` per RequestNext                |
| Block fetch request      | single point                            | list + NoMoreBlocks                |
| Tx bitmap                | CBOR map `{u16 => u64}` (indefinite)    | CBOR bytes, 9-octet roaring slices |
| Vote delivery            | push (batched array, in Notify)         | push (LeiosVotes protocol, single) |
| Merged/client block (N2C) | implemented in node; not on N2N path   | specified                          |

The vote format matches; everything else differs because the prototype predates
the CIP's protocol refactor. §9 and §10 split the gap by direction.

## 9. Prototype → CIP

Protocol-shape changes the **prototype** needs to converge on the current CIP.

| # | Change needed in the prototype | Now (prototype) | Target (CIP) | Refs |
|---|--------------------------------|-----------------|--------------|------|
| 1 | **Split `LeiosNotify` (ID 18)** into `LeiosAnnounce`, `LeiosVotes`, `LeiosBlockNotify` | one merged protocol | 3 protocols | §3, §6.7 |
| 2 | **Add `RequestNext(N)` token budget** to each notify-style protocol | no-arg `RequestNext` | `RequestNext(N)` | §6.7 |
| 3 | **Move votes to `LeiosVotes`** as single `MsgLeiosVote` pushes | batched `MsgLeiosVotes` array in Notify | one vote per message, own protocol | §6.7 |
| 4 | **Batch block fetch**: `MsgLeiosMultiBlockRequest` (list) + `MsgLeiosNoMoreBlocks` | single `MsgLeiosBlockRequest(point)` | multi-request + terminator | §6.8 |
| 5 | **Re-encode tx-bitmap** as the roaring byte-string (9-octet slices) | CBOR map `{u16 => u64}` | CBOR `bytes` | §6.8 |
| 6 | **Slim announcement/offer payloads** to `(slot, EB hash, block_height)` | full RB header / `point (+eb_size)` | tuple | §6.7 |
| 7 | **Implement the `leios_certificate`** — bitfield `signers` + aggregated BLS signature | mock `array(0)`/`null` | `[slot, hash, signers, aggregated_signature]` | §5.1, §4.3 |

**Already aligned (no work):** the vote format (stake-based `voter_id` + 48-B
MinSig, confirmed on the wire); no range/Genesis bulk-sync messages on either
side.

## 10. CIP → Prototype

Leaf-level encoding facts confirmed on the wire (and against source) that the
**CIP** should adopt or clarify — independent of the protocol refactor in §9.

| # | CIP should specify / change | Prototype wire reality | CIP today | Refs |
|---|------------------------------|------------------------|-----------|------|
| 1 | Make `announced_eb` an **explicit nested `array(2)`** `[hash32, uint32]` | one nested `array(2)` element (header = array(11)) | `? ( … )` **transparent group** = two flat entries (would be array(12)) | §4.2 |
| 2 | `eb_certificate` is **always present** (`null`/`array(0)` when absent), plus a trailing **`peras_cert`** slot → `era_block` = array(7) | always-present slots | `? eb_certificate` (omittable); no `peras_cert` | §4.3 |
| 3 | EB body is a **bare, definite CBOR map** `{hash32 => uint32}` (drop the array wrapper) | definite map, `encodeMapLen` | `[ omap<hash32, uint16> ]` | §4.4 |
| 4 | EB tx-size value is **uint32** (`encodeWord32`) | uint32 | `uint16` | §4.4 |
| 5 | `transaction_bodies` / `transaction_witness_sets` are **indefinite-length** arrays | indefinite | `[* … ]` (width-agnostic) | §4.3 |
| 6 | `MsgLeiosBlockTxs` reply **echoes `point` + `bitmap`** before the tx list | `[3, point, bitmap, [*tx]]` | reply carries only the tx list | §6.8 |
| 7 | Record the **mini-protocol number registry** (`LeiosNotify`=18, `LeiosFetch`=19) | IDs 18 / 19 (fixed in source) | no numbers assigned | §3 |
| 8 | Specify the EB **`point` as an explicit nested `array(2)`** `[slot, eb_hash]` (resolve [**cardano-blueprint#68**][cb68]) | nested `array(2)` (`encodeListLen 2`) | **transparent group** `(slot, eb_hash)` = two flat fields → decode/reset mismatch | §6.8 |

## 11. Not yet captured on the wire

The following are validated against the Haskell source but not yet observed on
the wire:

- `MsgLeiosBlockAnnouncement` (proto 18, tag 1) — incl. confirming its
  `announcement` payload is the full RB header.

A non-null certificate cannot be captured until the prototype implements one
(§9 row 7); today the `eb_certificate` slot is always `null`/`array(0)`.
