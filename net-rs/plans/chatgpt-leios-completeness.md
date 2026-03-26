# Cardano `net-rs` – Leios Protocol Support Review

**Branch:** `prc/net-rs`
**Scope:** Leios protocol support in `net-rs`, compared with **CIP-0164** mini-protocols
**Source of code truth:** supplied source tarball
**Exclusions:** Praos-only protocols already reviewed separately

---

# Executive Summary

`net-rs` has a **good protocol-level skeleton** for the Leios overlay described in CIP-0164.

In particular, it already has:

- the two proposed Leios mini-protocols:
  - `LeiosNotify` (protocol ID 18)
  - `LeiosFetch` (protocol ID 19)
- the expected state machines and core message families
- separation of notify vs fetch traffic
- basic peer-side integration in the multi-peer coordinator
- parsing support for Leios-related Praos header/body extensions

However, the implementation is **not yet complete to the CIP’s intended node behavior**.

The biggest remaining gaps are:

1. **LeiosFetch range support is only partial**
2. **Bitmap-selective transaction fetching is not actually implemented on the server path**
3. **Freshest-first delivery is not implemented as a library policy**
4. **Client-side pipelining is not implemented, despite the protocol shape allowing it**
5. **Leios block-announcement handling is not integrated end-to-end**
6. **Fetched Leios transactions / votes are not persisted back into the shared store for re-serving**

So the current best description is:

> `net-rs` is **protocol-complete enough for experimentation**, but **not yet behavior-complete** relative to CIP-0164.

---

# What Matches CIP-0164 Well

## 1. Two distinct Leios mini-protocols exist

The code implements the same two-protocol split proposed by CIP-0164:

- `LeiosNotify`
- `LeiosFetch`

This is a strong design choice because it preserves the intended separation between:

- low-latency announcements/offers
- larger fetch/retrieval traffic

That separation is central to the CIP’s feasibility argument.

---

## 2. `LeiosNotify` state machine matches the proposal

The implemented `LeiosNotify` protocol matches the CIP’s state-machine shape:

- `StIdle`
- `StBusy`
- `StDone`

with the expected transitions:

- client sends `MsgLeiosNotificationRequestNext`
- server replies with exactly one of:
  - `MsgLeiosBlockAnnouncement`
  - `MsgLeiosBlockOffer`
  - `MsgLeiosBlockTxsOffer`
  - `MsgLeiosVotesOffer`
- client may terminate with `MsgDone`

This is a close match to the CIP.

---

## 3. `LeiosFetch` state machine matches the proposal

The implemented `LeiosFetch` protocol also matches the CIP’s proposed state machine:

- `StIdle`
- `StBlock`
- `StBlockTxs`
- `StVotes`
- `StBlockRange`
- `StDone`

and supports the expected message families:

- block request / delivery
- block transactions request / delivery
- votes request / delivery
- certified block range request / streaming delivery

This is one of the strongest areas of the implementation.

---

## 4. Bitmap addressing is present in the protocol surface

`MsgLeiosBlockTxsRequest` carries:

- a `(slot, hash)` point
- a `BTreeMap<u16, u64>` bitmap map

This matches the CIP’s compact selective-fetch design and is the right wire-level abstraction.

---

## 5. Leios-specific Praos header/body extensions are understood

The type/parsing layer already handles the Leios extensions needed around Praos:

- RB headers can carry:
  - `announced_eb`
  - `announced_eb_size`
  - `certified_eb`
- block bodies can expose Leios-related info used to reconstruct block identity

This is important groundwork and appears well integrated in the parsing layer.

---

## 6. Praos / Leios separation is preserved in scheduling

In the actual peer protocol registration:

- Praos mini-protocols are `TrafficClass::Priority`
- Leios mini-protocols are `TrafficClass::Default(1)`

This supports the CIP’s requirement that Praos continue to make progress independently of Leios, and it is a sensible practical interpretation of the urgency separation described in the CIP.

---

# Where `net-rs` Is Only Partial

## 1. `LeiosFetch` range support exists in the protocol, but not end-to-end

### What exists

At the protocol layer:

- `MsgLeiosBlockRangeRequest`
- `MsgLeiosNextBlockAndTxsInRange`
- `MsgLeiosLastBlockAndTxsInRange`
- a client helper `fetch_block_range(...)`

### What is missing

At the integration layer:

- no coordinator-level command for Leios range fetches
- no peer-task command for range fetches
- no responder implementation of `MsgLeiosBlockRangeRequest`
- `serve_leios_fetch()` does not handle range requests

### Assessment

This means **range fetch is currently specified and coded at the protocol layer, but not operationally wired through the node stack**.

---

## 2. Bitmap-selective TX delivery is not implemented server-side

The CIP’s design makes selective transaction retrieval important for bandwidth efficiency.

### Current behavior

`serve_leios_fetch()` receives:

- `MsgLeiosBlockTxsRequest { point, bitmap }`

but ignores the bitmap entirely and responds with **all** stored transactions for that EB.

### Assessment

This is a meaningful gap.

The wire format is right, but the behavior is not yet compliant with the CIP’s intended semantics.

---

## 3. Notification support is incomplete for block announcements

`LeiosNotify` supports `MsgLeiosBlockAnnouncement` at the protocol level, and the client side can receive and forward it.

But the server-side notification store currently only produces:

- `BlockOffer`
- `BlockTxsOffer`
- `VotesOffer`

It does **not** currently persist and emit announcement-header notifications.

### Assessment

So:

- announcement **parsing and event plumbing** exist
- announcement **server-side generation and store integration** do not yet exist end-to-end

This matters because the CIP treats EB announcements via RB headers as a core part of Leios diffusion.

---

## 4. Client-side pipelining is not implemented

The CIP explicitly notes that:

- the client has agency only in one state
- therefore requests can be pipelined for latency hiding

### Current behavior

The current peer-side integration runs LeiosFetch via a single sub-task with an internal command channel and processes requests sequentially.

There is no visible support for:

- multiple outstanding requests on one runner
- pipeline depth control
- response matching for pipelined requests

### Assessment

This is not a protocol-shape problem.
It is an **execution-strategy gap**.

So `net-rs` currently has a **pipelineable** protocol, but not a **pipelined** implementation.

---

## 5. Freshest-first delivery is not implemented as node policy

The CIP is quite strong here: Leios correctness includes prioritizing younger data over older data, and the client should prefer the youngest outstanding offers when selecting fetches.

### Current behavior

The coordinator currently does useful things:

- deduplicates offers
- tracks which peers offered which objects
- prunes seen sets with a slot-bounded window
- selects fetch peers by lowest RTT among offering peers

But it does **not** itself implement a freshness scheduler such as:

- youngest-first offer queue
- explicit age-based request ordering
- deadline-aware prioritization of EB / TX / vote fetches

Instead, it forwards offers upward and leaves fetch choice largely to the application.

### Assessment

This is a major behavioral gap relative to the CIP.

It may be a deliberate layering choice, but if so it should be called out explicitly:

> freshest-first is currently an **application policy**, not a guaranteed property of `net-rs`

---

## 6. Vote delivery semantics are pragmatic, but weaker than ideal

For `MsgLeiosVotesRequest`, the server looks up whatever votes are present and returns the found subset.

### Concern

If the server previously offered those votes, then the strongest interpretation of the CIP would be that it should deliver them, not silently return fewer than requested.

### Assessment

This may be acceptable for an experimental implementation, but it is looser than ideal and could complicate caller assumptions.

---

# Important Missing Node-Behavior Pieces

These are the places where the implementation most clearly falls short of the CIP’s broader operational intent.

## 1. No OCIN / settled-window enforcement in the networking layer

The CIP’s node behavior text includes important constraints around which EB announcements should be considered, based on the settled ledger state and bounded OCIN windows.

I did not find end-to-end implementation of:

- ignoring announcements below settled OCIN
- ignoring announcements above settled+1
- bounded OCIN tracking / equivocation handling in the networking layer

### Assessment

This is a real node-behavior gap, though arguably above the raw mini-protocol layer.

---

## 2. No “download only the first EB announcement for a given opportunity” policy

The CIP says only the EB body corresponding to the **first** EB announcement / RB header received for a given creation opportunity should be downloaded.

I did not find explicit logic enforcing that policy in the coordinator.

### Assessment

Related deduplication exists, but this specific semantic rule does not appear to be implemented directly.

---

## 3. No store reinjection for fetched TXs and fetched votes

The shared `LeiosStore` can serve:

- blocks
n- block transactions
- votes

But in the current coordinator path:

- fetched blocks are injected back into the store
- fetched block transactions are **not** injected back into the store
- fetched votes are **not** injected back into the store

### Why this matters

That means a node can fetch Leios TXs or votes from one peer, but not automatically become a responder for those fetched objects.

### Assessment

This is a meaningful incompleteness in diffusion behavior.

---

# Overall Completeness Judgment

## Strong / complete enough

- protocol IDs and protocol split
- state-machine definitions
- CBOR message families
- notification/fetch separation
- Leios-related Praos header/body parsing
- basic offer deduplication and peer tracking
- fetch routing by offering peer + RTT

## Partial

- block announcements end-to-end
- vote semantics
- age-based prioritization
- transaction re-serving after fetch
- vote re-serving after fetch

## Clearly missing

- operational support for block range fetches
- bitmap-selective TX serving
- client-side pipelining
- OCIN / settled-window policy enforcement
- explicit “first-announcement-only” EB download policy

---

# Recommended Next Stages of Work

## Priority 1 — Make current protocol surface real

### A. Implement selective TX serving
- honor the bitmap in `MsgLeiosBlockTxsRequest`
- return only requested transactions

### B. Complete block-range support
- add coordinator/application command for range fetch
- add peer-task command path
- implement responder-side streaming for `MsgLeiosBlockRangeRequest`

### C. Reinject fetched TXs and votes into `LeiosStore`
- on `LeiosBlockTxsFetched`, call `inject_block_txs`
- on `LeiosVotesFetched`, call `inject_votes`

---

## Priority 2 — Complete notification behavior

### A. Add announcement notifications to `LeiosStore`
- persist RB-header announcement events
- serve `MsgLeiosBlockAnnouncement` from `serve_leios_notify()`

### B. Tighten vote request semantics
- decide whether missing offered votes should disconnect, error, or be explicit
- avoid silent partial success unless that is the intended contract

---

## Priority 3 — Implement actual Leios scheduling policy

### A. Freshest-first queueing
- prioritize youngest outstanding EB / TX / vote offers
- make the policy explicit in coordinator logic

### B. Opportunity-level deduplication
- enforce “first announcement for an opportunity wins” behavior

### C. Consider urgency separation inside Leios
- optionally split urgent range-sync traffic from less urgent traffic
- or use traffic-class overrides as suggested by the CIP discussion

---

## Priority 4 — Performance / full behavior

### A. Add LeiosFetch pipelining
- multiple outstanding requests
- pipeline depth control
- response handling strategy

### B. Add node-level OCIN filtering / bounded tracking
- settled-window checks
- bounded equivocation tracking

---

# Final Conclusion

> `net-rs` already has a **credible Leios mini-protocol foundation**, but it is **not yet complete to CIP-0164 node-behavior expectations**.

The code is strongest at the **protocol/state-machine level**.
The main remaining work is in:

- **end-to-end integration**
- **behavioral policy (freshest-first)**
- **full fetch semantics**
- **pipelining / performance**

A good working description for the next stage is:

> **Protocol-complete skeleton, behaviorally partial implementation.**

