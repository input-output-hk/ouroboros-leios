# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Rust implementation of the Cardano mini-protocol network stack for Praos and Leios protocols. This is a greenfield project — see `plans/masterplan.md` for the full vision.

### Goals

- Network prototyping and simulation
- Adversarial node support
- Fast Leios on-ramp for downstream tools (Acropolis, Dolos, Ogmios)
- Reference design for node implementors

## Build & Test Commands

```sh
cargo build                    # build
cargo test                     # run all tests
cargo clippy                   # lint
cargo fmt --check              # format check
```

## Testing

```sh
cargo test                     # run all unit + integration tests
cargo run -p net-cli -- handshake backbone.cardano.iog.io:3001  # live test against mainnet
cargo run -p net-cli -- capture backbone.cardano.iog.io:3001    # capture wire bytes for test vectors
```

### Test vector workflow

When implementing a new protocol or changing CBOR encoding:

1. Use `net-cli capture` (or write a similar capture command) to record the raw bytes exchanged with a real Cardano node
2. Add the captured bytes as `const` test vectors in the relevant codec test module
3. Write tests that: (a) decode the captured bytes, (b) verify our encoding matches the captured bytes, (c) round-trip our types through encode/decode
4. This ensures wire compatibility with the live network, not just self-consistency

Test data notes are in `net-core/test_data/README.md`.

## Code Standards

- **No panics** — every `unwrap()`, `expect()`, indexing, etc. must be handled. Use `Result`/`Option` propagation.
- **Simplicity over concision** — code must be legible to non-Rust developers. When there's a choice, be explicit.
- **Minimal dependencies** — no C-binding dependencies. Any significant new dependency must be discussed with a human first.
- **Stable Rust only** — no nightly or unstable features.
- **High performance, high security** — avoid unnecessary allocations, copies, and unsafe code.

## Architecture Notes

### Multiplexing

Cardano mini-protocols are carried over a single multiplexed TCP socket per node pair (per direction if duplexed). Leios introduces large messages that can head-of-line block time-critical Praos messages, so the multiplexer needs QoS facilities:

- Strict priority by protocol ID (DiffServ-like)
- Weighted fair queuing (WFQ)
- Pluggable and configurable

### Codecs

Messages use CBOR encoding (CDDL-specified). The multiplexing protocol has no framing bits for message boundaries — we need an efficient solution rather than successive decode attempts.

### Timeouts

Protocol timeouts must be implemented and enforced, both detection and handling.

### Alternate Transports

The bearer/transport layer must be trait-based and pluggable. Current scope is TCP only (no Unix sockets / N2C), but the design must not block future transports (Unix sockets, QUIC, etc.).

## Implementation Phases

1. **Phase 1: Basic Handshake** — multiplexer + Handshake protocol + CLI test connecting to an existing node
2. **Phase 2: ChainSync / BlockFetch** — ChainSync and BlockFetch protocols + CLI test that follows tip and fetches blocks

## Documentation

- `docs/praos-network.md` — protocol reference: multiplexer wire format, all six N2N mini-protocols (state machines, CBOR CDDL, timeouts, size limits), concrete Cardano era-tagged types
- `docs/implementation-haskell.md` — how ouroboros-network implements the protocols: mux architecture (Wanton + round-robin), typed-protocol framework, connection manager, per-protocol notes
- `docs/implementation-pallas-v1.md` — how pallas-network v1 implements them: facade API, multiplexer, codec patterns, design assessment with strengths/weaknesses for our use case
- `docs/implementation-pallas-v2.md` — how pallas-network2 redesigns them: Interface/Behavior/Manager layering, pure state machines, visitor pattern, promotion system, comparison tables
- `docs/leios-changes.md` — CIP-0164 Leios additions: new protocols (LeiosNotify, LeiosFetch), modified Praos headers/blocks, new data types (EB, votes, certificates, BLS), QoS/priority requirements, and structural implications for net-rs
- `plans/implementation-plan.md` — Phase 1 plan: workspace structure, layer design (bearer, mux, codec, protocol framework, handshake), implementation order, verification strategy

## References

- [Cardano network spec (Praos)](https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf)
- [Cardano blueprint](https://cardano-scaling.github.io/cardano-blueprint/network/index.html)
- [CIP-0164 Leios spec](https://cips.cardano.org/cip/CIP-0164#network)
- [Haskell ouroboros-network](https://github.com/IntersectMBO/ouroboros-network) — live Praos deployment
- [Pallas v1](https://github.com/txpipe/pallas/tree/main/pallas-network) / [v2](https://github.com/txpipe/pallas/tree/main/pallas-network2) — existing Rust implementations
