# Cardano `net-rs` – Praos N2N Spec Completeness Review

[Note: Taken EOD 26/3/26 after bb00678e03 Risk Register signoff]

**Branch:** `prc/net-rs`
**Scope:** Ouroboros Praos **node-to-node (N2N)** networking only
**Exclusions:**
- Node-to-client (N2C) protocols (deliberately out of scope)
- Leios protocols (ignored for this analysis)

---

# Executive Summary

The `net-rs` networking stack is now:

> **A largely complete and spec-aligned implementation of the Praos node-to-node mini-protocol layer.**

All previously identified correctness and safety issues have been addressed. The implementation now aligns well with the Ouroboros network specification at the **protocol, mux, and wire levels**.

The remaining gaps are **not correctness issues**, but instead fall into two clearly defined areas:

- **Connection management / peer governor (system-level orchestration)**
- **Protocol pipelining (performance and throughput)**

---

# What Is Complete and Spec-Aligned

## 1. Mini-Protocol Surface

All core Praos N2N protocols are implemented:

- ChainSync
- BlockFetch
- TxSubmission v2
- KeepAlive
- PeerSharing

Protocol IDs, message flows, and roles align with the spec.

---

## 2. Handshake and Version Negotiation

- Supports current node-to-node versions (V14, V15)
- Negotiates:
  - `networkMagic`
  - diffusion mode
  - peer sharing
- Correct use of `VersionData`
- Proper negotiation semantics (including diffusion mode OR)

---

## 3. Mux Layer

Fully aligned with spec expectations:

- Segment-based framing
- Protocol ID routing
- Full duplex communication
- Per-mini-protocol queues
- Ingress buffer limits using spec values

---

## 4. Scheduling (Important Clarification)

The scheduler supports multiple policies, including `PriorityWfq`.

However:

> **All Praos protocols are assigned `TrafficClass::Priority`**

This results in:

- Effective **round-robin scheduling across Praos protocols**
- One SDU per protocol per scheduling turn

### Conclusion

- ✔ Matches spec requirement for fair scheduling
- ✔ No starvation within Praos protocols
- ⚠ WFQ only applies to non-Praos traffic (e.g. Leios)

---

## 5. Message Size Limits

- Per-state message size limits enforced dynamically
- Applied at receive path (before decode completion)
- Updated on state transitions

### Alignment

Matches the Haskell node model:
- state-dependent limits
- enforced during decoding
- connection teardown on violation

---

## 6. Timeouts

Per-protocol timeouts align with spec values:

- Handshake: 10s
- ChainSync, BlockFetch, KeepAlive, PeerSharing: spec-consistent values

Timeouts are enforced and violations lead to disconnect.

---

## 7. BlockFetch Correctness

- Block identity derived from block body
- No reliance on request range endpoints
- Proper header/body linkage

---

## 8. Admission Control (Application Layer)

Implemented mechanisms include:

- Decoupled accept and handshake
- Bounded concurrent handshakes (semaphore)
- Per-IP connection limits
- Proper cleanup on failure/disconnect

### Interpretation

This provides **appropriate application-level protection against adversarial peers**, without duplicating firewall responsibilities.

---

## 9. Transport Robustness

- TCP keepalive enabled
- No busy-wait loops (Notify-based wakeup)
- Clean async design

---

# Remaining Gaps

These are the **next-stage work areas**.

---

## A. Connection Manager / Peer Governor

### Status: Not implemented

The Ouroboros network spec defines a higher-level orchestration layer that is not yet present.

### Spec Features

- Peer states:
  - cold / warm / hot
- Promotion and demotion logic
- Peer quality evaluation
- Connection churn control
- Inbound protocol governor
- On-demand responder startup
- Idle handling:
  - ~5s inbound protocol start timeout
  - ~60s post-idle reset

### Current `net-rs`

- Basic peer coordination
- Admission control
- Multi-peer connections

### Missing

- Peer lifecycle state machine
- Dynamic peer selection / ranking
- Promotion/demotion policies
- Idle-state transitions
- Protocol activation governance

### Interpretation

This is:

> **A system-level layer above the networking stack**

It is not required for protocol correctness but is required for:

- production-grade network behaviour
- resilience
- efficient peer utilisation

---

## B. Protocol Pipelining

### Status: Not implemented

### Spec Expectation

Modern N2N protocols support pipelining:

- Multiple outstanding requests
- Pipeline depth control
- Overlapping request/response cycles

### Current Behaviour

- Strict request/response (non-pipelined)
- No pipeline depth tracking
- No out-of-order response handling

### Impact

| Aspect        | Status |
|---------------|--------|
| Correctness   | ✅ OK |
| Spec fidelity | ⚠ Partial |
| Performance   | ❌ Limited |

### Interpretation

This is:

> **A performance and completeness enhancement, not a correctness requirement**

---

# Non-Issues / Clarifications

## Scheduler Fairness

- Praos protocols are effectively round-robin
- WFQ does not affect Praos behaviour
- No spec violation

---

## Timeout Configuration

- Extended timeouts (e.g. 900s) are operational overrides
- Spec defines defaults, not strict requirements

---

## Version Support

- Supporting V14/V15 only is acceptable
- Historical versions are not required for spec compliance

---

## Node-to-Client

- Explicitly out of scope
- Not considered a gap

---

# Recommended Next Steps

## Priority 1: Connection Manager / Governor

Define architecture for:

- Peer state tracking (cold/warm/hot)
- Promotion/demotion rules
- Peer quality metrics
- Inbound protocol governance
- Idle connection management

Suggested approach:
- Keep this as a **separate layer above `net-core`**
- Avoid entangling protocol logic with policy

---

## Priority 2: Pipelining

Add pipelined execution for:

- ChainSync
- BlockFetch

Key requirements:

- Track outstanding requests
- Handle responses asynchronously
- Respect protocol state machine constraints

---

## Optional Enhancements

- Improved logging around rare edge cases (e.g. missing headers)
- Future refinement of deduplication strategy (Leios)

---

# Final Conclusion

> **`net-rs` is now complete at the Praos node-to-node protocol and mux layer.**

The remaining work is:

- **System-level orchestration (governor)**
- **Performance-level improvements (pipelining)**

No remaining gaps affect protocol correctness or basic spec compliance.

---
