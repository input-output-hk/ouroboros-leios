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
cargo run -p net-cli -- serve --port 9999 --block-rate 0.05     # fake server (Poisson blocks)
cargo run -p net-cli -- follow 127.0.0.1:9999                   # follow fake server
cargo run -p net-cli -- submit 127.0.0.1:9999                   # submit tx to fake server
cargo run -p net-cli -- peer-share cardano-main2.everstake.one:3001  # peer sharing (live, supports peer_sharing=1)
```

### Test vector workflow

When implementing a new protocol or changing CBOR encoding:

1. Use `net-cli capture` (or write a similar capture command) to record the raw bytes exchanged with a real Cardano node
2. Add the captured bytes as `const` test vectors in the relevant codec test module
3. Write tests that: (a) decode the captured bytes, (b) verify our encoding matches the captured bytes, (c) round-trip our types through encode/decode
4. This ensures wire compatibility with the live network, not just self-consistency

Test data notes are in `net-core/test_data/README.md`.

### Security audit at end of each phase

Before marking a phase complete, audit every path where untrusted remote data enters the system:

1. **Allocation bounds**: every length field read from the wire (CBOR map/array lengths, segment payload_len, string lengths) must be checked against a maximum before allocating. A malicious peer must not be able to trigger unbounded allocation.
2. **Buffer bounds**: every accumulation buffer (codec recv buffer, ingress buffers) must have a hard cap. Exceeding it must return an error, not block or grow.
3. **No blocking on untrusted input**: the demuxer must never block waiting for a slow protocol consumer (use `try_send`, not `send().await`). A single slow/malicious protocol must not stall others.
4. **Timeout coverage**: every state where we wait for remote data must have a timeout. Verify no path can wait forever.
5. **Error propagation**: every error must result in clean connection teardown. Verify no error is silently swallowed leaving the connection in a broken state.
6. **No panics**: `grep` for `unwrap()`, `expect()`, `panic!`, indexing without bounds checks in non-test code.

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

## Workspace Structure

```
net-rs/
  Cargo.toml            -- workspace root
  net-core/             -- library crate
    src/
      lib.rs
      bearer/           -- Bearer trait (mod.rs), TcpBearer (tcp.rs), MemBearer (mem.rs)
      mux/              -- Multiplexer: wire format, egress/ingress tasks, channels, scheduler
      codec.rs          -- CBOR framing over mux channels (CodecSend/CodecRecv)
      protocol.rs       -- Protocol trait, Runner with agency-checked send/recv
      types.rs          -- Shared Cardano types: Point, Tip, WrappedHeader, BlockBody
      protocols/
        handshake/      -- Handshake protocol (state machine, CBOR codec, N2N version data)
        chainsync/      -- ChainSync protocol (follow chain tip, intersection finding)
        blockfetch/     -- BlockFetch protocol (request and stream block ranges)
        keepalive/      -- KeepAlive protocol (ping/pong to keep connections alive)
        txsubmission/   -- TxSubmission protocol (pull-based tx dissemination, blocking/non-blocking)
        peersharing/    -- PeerSharing protocol (peer discovery, IPv4/IPv6 addresses)
  net-cli/              -- binary crate
    src/
      main.rs           -- subcommand dispatch
      connect.rs        -- shared connection helper (TCP + mux + handshake)
      handshake.rs      -- `handshake` command (connect + negotiate)
      capture.rs        -- `capture` command (raw byte capture for test vectors)
      chainsync.rs      -- `chain-sync` command (follow chain tip)
      blockfetch.rs     -- `block-fetch` command (fetch blocks)
      follow.rs         -- `follow` command (persistent chain follower with reconnect)
      serve.rs          -- `serve` command (fake server with all 6 N2N protocols)
      submit.rs         -- `submit` command (tx submission with Poisson generation)
      peershare.rs      -- `peer-share` command (request peers from a node)
```

## Key Design Decisions

- **Bearer**: trait-based (not enum) for transport pluggability
- **Mux**: per-protocol egress queues with pluggable Scheduler trait; demuxer uses `try_send` (never blocks); supervisor auto-aborts peer on task failure
- **Ingress accounting**: shared `Arc<AtomicUsize>` between demuxer and ChannelRecv for accurate buffer tracking
- **Codec**: `for<'a> Decode<'a>` (HRTB) so decoded types are owned, avoiding borrow conflicts; `max_buffer` cap prevents unbounded growth
- **Protocol framework**: `Runner` wraps codec + state, provides agency-checked `send()`/`recv()` — protocols use it directly in async functions (not a generic driver loop)
- **SDU size**: default 12,288 bytes (Cardano standard), not 65,535
- **Opaque headers/blocks**: `WrappedHeader` and `BlockBody` store raw CBOR bytes — era-specific decoding happens at higher layers, not the network stack
- **Composable client helpers**: protocols expose simple async functions (`find_intersection`, `request_next`, `recv_block`) rather than complex callback frameworks
- **Server uses Message directly**: server-side code uses `runner.recv()` / `runner.send()` with Message enums — no separate Request/Response types (Runner enforces agency)

## Implementation Phases

1. **Phase 1: Mux + Handshake** — COMPLETE. Bearer, mux, codec, protocol framework, handshake (client+server), CLI, 51 tests, live-tested against mainnet, security-audited.
2. **Phase 2: ChainSync / BlockFetch** — COMPLETE. Shared types (Point, Tip, WrappedHeader, BlockBody), ChainSync + BlockFetch + KeepAlive protocols (state machines, CBOR codecs, client + server), persistent chain follower with reconnection, fake server CLI with Poisson block/rollback generation, 109 tests, live-tested against mainnet, security-audited.
3. **Phase 3: Remaining Praos + Multi-Peer** — PROTOCOLS COMPLETE. TxSubmission (6 states, pull-based with blocking/non-blocking, flow control, client helper + server handler, 20 tests) and PeerSharing (3 states, IPv4/IPv6 peer addresses, client helper + server handler, 18 tests). All 6 N2N mini-protocols implemented. 147 total tests. Live-tested against mainnet (PeerSharing against cardano-main2.everstake.one:3001). Multi-peer coordination layer still TBD.
4. **Phase 4: Leios Protocols** — LeiosNotify, LeiosFetch, priority scheduling

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
