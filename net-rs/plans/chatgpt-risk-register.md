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
Removed `point` from `PeerEvent::BlockFetched` — the block body contains the header, so point derivation is the coordinator's responsibility. Added `BlockBody::point()` which extracts the header from the block, parses it for slot (via `HeaderInfo`), and computes Blake2b-256 of the header CBOR for the block hash. Added `blake2b_simd` dependency (pure Rust). Coordinator now calls `body.point()` to derive correct points for each streamed block. Commit: PENDING

---

## 4. Weak Peer Selection for BlockFetch

**Severity:** High
**Status:** Open

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

---

## 5. Fail-Open Deduplication in Leios

**Severity:** Medium–High
**Status:** Open

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

---

## 6. Egress Busy-Wait Scheduling

**Severity:** Medium
**Status:** Open

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

---

## 7. Strict Priority Scheduling Starvation

**Severity:** Medium
**Status:** Open

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
