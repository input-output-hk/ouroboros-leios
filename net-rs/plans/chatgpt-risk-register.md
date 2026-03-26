# Cardano `net-rs` Risk Register (prc/net-rs)

This document outlines identified risks in the `net-rs` networking library, focusing on structure, specification adherence, and resilience against adversarial peers.

---

## 1. Missing Enforcement of Per-State Message Size Limits

**Severity:** High
**Status:** Fixed

### Description
Protocol-defined message size limits are not enforced at the protocol runner level, leaving only coarse mux-level limits.

### Details
- `Protocol::size_limit()` exists but is not enforced in `Runner::recv()`.
- Enforcement falls back to mux codec max buffer (~2.5MB).
- Violates Cardano mini-protocol expectation of **state-dependent bounds**.
- Enables adversarial peers to:
  - Send oversized but still “under mux cap” messages
  - Trigger excessive allocation / decode cost
- Particularly relevant for:
  - BlockFetch (large bodies)
  - ChainSync roll-forward payloads

### Risk
- Memory pressure / DoS
- Spec deviation (state-machine constraints bypassed)

### Resolution
Per-state size limits now enforced at demuxer level (one hop from TCP socket), before data enters protocol buffers. Shared `IngressLimit` atomic updated by `Runner` on every state transition; demuxer reads it on every segment dispatch. TCP backpressure naturally constrains sender when limits are hit. Redundant codec `max_buffer` (hardcoded 2.5MB) removed — it was both redundant and harmful for LeiosFetch 16MB messages. `Protocol::size_limit()` is now a required trait method (must return nonzero); Runner panics at construction if violated. Commit: 32c2ea936

---

## 2. Incorrect Handshake Capability Advertisement

**Severity:** High
**Status:** Fixed

### Description
Handshake negotiation advertises capabilities that do not match actual behaviour.

### Details
- `peer_sharing = 0` even though PeerSharing protocol exists
- `initiator_only_diffusion_mode = false` in non-duplex path
- Capability surface != implementation surface
- Can lead to:
  - Missed peer-sharing opportunities (network inefficiency)
  - Incorrect expectations by remote peers
- Diverges from node-to-node handshake spec expectations

### Risk
- Network topology degradation
- Interoperability inconsistencies
- Hard-to-debug peer behaviour

### Resolution
- `peer_sharing` now set to `1` in all paths (PeerSharing protocol is always registered)
- `initiator_only_diffusion_mode` now `true` for InitiatorOnly connections, `false` for Duplex
- `negotiate()` now takes server `VersionData` and correctly ORs diffusion modes per spec
- Added `negotiate_diffusion_mode_or` test verifying both client-only and server-only proposals
- Commit: 207e0a2a7

---

## 3. BlockFetch Point Misattribution

**Severity:** High
**Status:** Fixed

### Description
Fetched blocks are not associated with their correct chain points.

### Details
- `PeerEvent::BlockFetched` uses **range end point** for all returned blocks
- Code comment explicitly acknowledges missing exact mapping
- Coordinator compensates with:
  - `pending_headers` lookup
  - fallback to empty CBOR map
- Breaks invariant:
  - “block ↔ header ↔ point” must be exact

### Risk
- Incorrect chain assembly
- Potential ledger inconsistency
- Attack surface:
  - Malicious peer can reorder or inject ambiguous blocks

### Resolution
Removed `point` from `PeerEvent::BlockFetched` — the block body contains the header, so point derivation is the coordinator's responsibility. Added `BlockBody::point()` which extracts the header from the block, parses it for slot (via `HeaderInfo`), and computes Blake2b-256 of the header CBOR for the block hash. Added `blake2b_simd` dependency (pure Rust). Coordinator now calls `body.point()` to derive correct points for each streamed block. Commit: 8ddb06048

---

## 4. Weak Peer Selection for BlockFetch

**Severity:** High
**Status:** Fixed

### Description
Peers are selected for block fetch without strong evidence they contain the requested data.

### Details
- Eligibility condition:
  - peer tip == point OR
  - peer has any nonzero block number
- No requirement for:
  - Known intersection
  - Proven range coverage
- Essentially “any alive peer” qualifies

### Risk
- Inefficient fetching
- Increased latency
- Adversarial peers can:
  - Stall requests
  - Feed partial or irrelevant data

### Resolution
Per-peer `ChainFragment` now tracks the exact set of points announced via ChainSync. Each fragment is built from the intersection point (surfaced via new `PeerEvent::IntersectionFound`), extended on each `HeaderAnnounced`, truncated on `RolledBack`, and pruned per-point on `BlockFetched`. Fetch routing now requires `fragment.contains(&point)` — only peers who provably announced the requested block are eligible. Added `WrappedHeader::point()` (shared `header_hash` helper with `BlockBody::point()`) to correctly derive header points, fixing a pre-existing `pending_headers` keying bug that used `tip.point` instead of the announced header's point. `PeerEvent::BlockFetchFailed` and `NetworkEvent::BlockFetchFailed` surface NoBlocks responses to the application for retry. Commit: 3683da78e

---

## 5. Fail-Open Deduplication in Leios

**Severity:** Medium–High
**Status:** Accepted

### Description
Deduplication mechanisms degrade under load, allowing duplicate traffic.

### Details
- “seen” and “offer” sets capped (~100k entries)
- When full → **fail-open behaviour**
- Explicitly documented in code
- Adversary can:
  - Flood identifiers
  - Exhaust dedup capacity
  - Reintroduce duplicate propagation

### Risk
- Amplified network traffic
- Reduced effectiveness of anti-duplication
- Potential cascading load issues

### Resolution
Accepted as intentional design. Fail-open is the correct safety valve — fail-closed would allow an adversary to fill the seen set with fabricated offers and thereby suppress legitimate ones. Slot-based pruning (`update_leios_slot`, window default 1000 slots) is the primary bound and keeps sets well under 100K during normal operation. To reach the hard cap an adversary would need 100+ unique offers per slot sustained across the window; the consequence is only duplicate forwarding to the application, which must still decide whether to fetch (and fake offers fail at fetch time). The targeted defence against a flooding adversary is per-peer rate limiting / admission control, which belongs in future peer management work (Phase 3b promotion/demotion/churn).

---

## 6. Egress Busy-Wait Scheduling

**Severity:** Medium
**Status:** Fixed

### Description
Mux egress uses a polling loop with `yield_now()` instead of event-driven wakeups.

### Details
- `wait_for_any_data()` = poll + yield loop
- Lacks:
  - `Notify` / waker-based signalling
- Under load:
  - CPU inefficiency
  - Scheduler churn
- Worse under adversarial conditions:
  - many idle protocols
  - sporadic bursts

### Risk
- CPU waste
- Reduced scalability
- Potential performance degradation under attack

### Resolution
Replaced `yield_now()` polling loop with a shared `tokio::sync::Notify` per Mux instance. `ChannelSend::send()` signals `notify_one()` after queuing data; the egress loop registers `notified()` before checking receivers (avoiding the race between check and wait), then blocks on the notify or a 100ms timeout for closed-channel cleanup. One Notify per Mux (not per protocol) — only one egress task consumes, so no thundering herd. Commit: 7072a573d

---

## 7. Strict Priority Scheduling Starvation

**Severity:** Medium
**Status:** Fixed

### Description
Scheduler allows indefinite starvation of lower-priority protocols.

### Details
- Strict priority (no fairness mechanism)
- Known and documented behaviour
- High-priority traffic can dominate indefinitely
- Example:
  - control traffic floods suppress data protocols

### Risk
- Effective denial-of-service on lower-priority protocols
- Reduced system utility under load
- Trade-off currently biased too far toward priority

### Resolution
Added `PriorityWfq` two-class scheduler as the new default. Protocols are assigned to either Priority class (absolute priority, round-robin among peers) or Default class (message-based weighted fair queuing). Praos protocols (Handshake, ChainSync, BlockFetch, TxSubmission, KeepAlive) are Priority class; Leios protocols and PeerSharing are Default class with configurable weights. Default class is only serviced when no Priority protocol has data, but within Default class, each protocol gets turns proportional to its weight — preventing starvation among Leios protocols. `StrictPriority` and `RoundRobin` schedulers retained as simpler alternatives. Per-protocol traffic class overrides available via `--protocol-priority` CLI flag. `ProtocolConfig.priority` replaced by `ProtocolConfig.traffic_class: TrafficClass` enum (`Priority | Default(weight)`). Commit: TBD

---

## 8. Missing TCP Keepalive Configuration

**Severity:** Medium
**Status:** Open

### Description
TCP connections are not configured with keepalive despite documentation implying it.

### Details
- `TCP_NODELAY` set
- Keepalive not configured
- Relies on:
  - protocol-level keepalive
  - timeouts
- OS-level dead peer detection not utilised

### Risk
- Slow detection of half-open connections
- Resource leakage (sockets, peer slots)
- Increased exposure to connection exhaustion

---

## 9. Weak Inbound Admission Control

**Severity:** Medium–High
**Status:** Open

### Description
Inbound connection handling lacks early-stage defensive controls.

### Details
- Accepts connections until `max_peers`
- Excess connections dropped, but:
  - no per-IP limits
  - no rate limiting
  - no handshake throttling
- No protection against:
  - connection floods
  - handshake abuse

### Risk
- Connection exhaustion
- Resource starvation
- Vulnerability to simple DoS attacks

---

## 10. Ambiguous “Not Found” Semantics in Leios Fetch

**Severity:** Medium
**Status:** Open

### Description
Missing data is represented as empty payload instead of explicit absence.

### Details
- `unwrap_or_default()` used for missing blocks/transactions
- Collapses:
  - “not found”
  - “empty but valid”
- Leios protocol still evolving (CIP-stage)
- Risk increases if semantics become fixed later

### Risk
- Ambiguous protocol behaviour
- Future incompatibility with spec
- Harder debugging and validation

---

## 11. Incomplete Client-Side Protocol Coverage

**Severity:** Low–Medium
**Status:** Open

### Description
Not all implemented protocols are wired into the client orchestration layer.

### Details
- TxSubmission present in protocol layer
- Not integrated in peer client orchestration
- Asymmetry:
  - server supports more than client uses

### Risk
- Functional incompleteness
- Misleading documentation claims
- Reduced test coverage of full protocol set

---

# Summary

## Critical (Must Fix)
- Per-state size limit enforcement
- Handshake correctness
- BlockFetch correctness
- Peer selection logic

## Important (Robustness / Adversarial Resilience)
- Deduplication fail-open behaviour
- Admission control
- Scheduling fairness
- Egress wakeup model

## Secondary (Correctness / Completeness)
- TCP keepalive
- Leios response semantics
- Protocol wiring completeness

---
