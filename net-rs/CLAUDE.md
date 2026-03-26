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
cargo run -p net-cli -- multi-follow --host backbone.cardano.iog.io:3001 --host backbone.cardano.iog.io:3001  # multi-peer follow (live)
cargo run -p net-cli -- multi-follow --host backbone.cardano.iog.io:3001 --listen 0.0.0.0:8888  # relay mode (live upstream, local downstream)
cargo run -p net-cli -- serve --port 9999 --block-rate 0.5 --leios  # fake server with Leios EB/vote generation
cargo run -p net-cli -- multi-follow --host 127.0.0.1:9999 --leios  # follow with Leios notifications
RUST_LOG=debug cargo run -p net-cli -- multi-follow --host 127.0.0.1:9999 --host 127.0.0.1:9999 --leios  # multi-peer Leios dedup (two connections, observe dedup/routing logs)
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
      mux/              -- Multiplexer: wire format, egress/ingress tasks, channels, scheduler, CBOR codec
        codec.rs        -- CBOR framing over mux channels (CodecSend/CodecRecv)
      types/            -- Shared Cardano types
        mod.rs          -- Point, Tip, encode/decode_points
        header.rs       -- WrappedHeader, HeaderInfo (Shelley+ header parser with Leios extensions)
        block.rs        -- BlockBody, LeiosBlockInfo (block body parser)
      protocols/
        protocol.rs     -- Protocol trait, Runner with agency-checked send/recv
        handshake/      -- Handshake protocol (state machine, CBOR codec, N2N version data)
        chainsync/      -- ChainSync protocol (follow chain tip, intersection finding)
        blockfetch/     -- BlockFetch protocol (request and stream block ranges)
        keepalive/      -- KeepAlive protocol (ping/pong to keep connections alive)
        txsubmission/   -- TxSubmission protocol (pull-based tx dissemination, blocking/non-blocking)
        peersharing/    -- PeerSharing protocol (peer discovery, IPv4/IPv6 addresses)
        leios_notify/   -- LeiosNotify protocol (Leios announcement, protocol ID 18)
        leios_fetch/    -- LeiosFetch protocol (Leios data fetch with bitmap TX addressing, protocol ID 19)
      peer/
        mod.rs            -- PeerId, ConnectionMode, CoordinatorConfig, CoordinatorHandle, PeerError
        types.rs          -- PeerEvent, PeerCommand, NetworkEvent, NetworkCommand
        chain_store.rs    -- ChainStore: shared in-memory chain state for responder peers
        connect.rs        -- connection helpers (TCP + mux + handshake, moved from net-cli)
        peer_task.rs      -- per-peer initiator task: client protocol sub-tasks
        responder_task.rs -- per-peer responder task: server protocol sub-tasks
        duplex_task.rs    -- per-peer duplex task: both client + server on one connection
        leios_store.rs    -- LeiosStore: content-addressed store for Leios data (EBs, votes)
        server_handlers.rs -- server-side protocol handlers (ChainSync/BlockFetch/KeepAlive/TxSubmission/PeerSharing/LeiosNotify/LeiosFetch)
        coordinator.rs    -- coordinator: peer aggregation, tip dedup, fetch routing, accept loop, reconnection
  net-cli/              -- binary crate
    src/
      main.rs           -- subcommand dispatch
      connect.rs        -- re-exports net_core::peer::connect
      handshake.rs      -- `handshake` command (connect + negotiate)
      capture.rs        -- `capture` command (raw byte capture for test vectors)
      chainsync.rs      -- `chain-sync` command (follow chain tip)
      blockfetch.rs     -- `block-fetch` command (fetch blocks)
      follow.rs         -- `follow` command (persistent single-peer chain follower)
      multi_follow.rs   -- `multi-follow` command (multi-peer chain follower via coordinator, --listen, --duplex)
      serve.rs          -- `serve` command (fake server via coordinator with Poisson block generation)
      submit.rs         -- `submit` command (tx submission with Poisson generation)
      peershare.rs      -- `peer-share` command (request peers from a node)
```

## Key Design Decisions

- **Bearer**: trait-based (not enum) for transport pluggability
- **Mux**: per-protocol egress queues with pluggable Scheduler trait; demuxer uses `try_send` (never blocks); supervisor auto-aborts peer on task failure
- **Ingress accounting**: shared `Arc<AtomicUsize>` between demuxer and ChannelRecv for accurate buffer tracking; shared `IngressLimit` atomic allows Runner to update per-state size limits at the demuxer (closest to TCP socket)
- **Codec**: `for<'a> Decode<'a>` (HRTB) so decoded types are owned, avoiding borrow conflicts
- **Protocol framework**: `Runner` wraps codec + state, provides agency-checked `send()`/`recv()` — protocols use it directly in async functions (not a generic driver loop). Runner updates demuxer ingress limit on every state transition. `Protocol::size_limit()` is a required trait method (must return nonzero)
- **SDU size**: default 12,288 bytes (Cardano standard), not 65,535
- **Parsed headers, opaque blocks**: `WrappedHeader` stores raw CBOR bytes plus parsed `HeaderInfo` (Shelley+ era, slot, block_number, prev_hash, issuer_vkey, body_size, block_body_hash, CIP-0164 Leios extensions). `BlockBody` stores raw bytes plus parsed `LeiosBlockInfo` (EB certificate if present). Byron headers/blocks return `None` gracefully. Parsing uses array-length disambiguation for optional Leios fields (10=base, 11=certified_eb, 12=announced_eb, 13=both)
- **Composable client helpers**: protocols expose simple async functions (`find_intersection`, `request_next`, `recv_block`) rather than complex callback frameworks
- **Server uses Message directly**: server-side code uses `runner.recv()` / `runner.send()` with Message enums — no separate Request/Response types (Runner enforces agency)
- **Multi-peer coordinator**: thread-per-peer with shared coordinator task. Each peer runs an independent tokio task tree; coordinator aggregates state via channels. Per-peer tasks fan-in `(PeerId, PeerEvent)` to coordinator; coordinator sends `PeerCommand` per-peer. Application interface is peer-agnostic (`NetworkEvent`/`NetworkCommand`). Three connection modes: InitiatorOnly (outbound, client protocols), ResponderOnly (inbound, server protocols), Duplex (both on one connection). Mux uses `(ProtocolId, u16)` composite keys to support both directions per protocol ID. ChainStore shared between coordinator and responder/duplex peers; populated via `InjectBlock`/`InjectRollback` commands or from initiator peer `BlockFetched` events. Accept loop for inbound connections via `listen_address` config. Exponential backoff reconnection for initiator/duplex peers; no reconnection for responder peers.
- **Leios per-peer integration**: `leios_enabled: bool` config flag (default false). When true, per-peer tasks register LeiosNotify (ID 18) and LeiosFetch (ID 19) alongside Praos protocols. `spawn_leios_notify` runs continuous request_next loop; `spawn_leios_fetch` is command-driven (like BlockFetch). Server handlers `serve_leios_notify`/`serve_leios_fetch` read from `LeiosStore`. `LeiosStore` is a content-addressed blob store separate from `ChainStore` (Leios data keyed by `(slot, hash)`, not part of a linear chain).
- **Leios coordinator intelligence**: Coordinator deduplicates EB, TX, and vote offers across peers using slot-bounded seen sets (configurable `leios_dedup_window`, default 1000 slots). Tracks which peers offered which data for RTT-based smart fetch routing (mirrors Praos `FetchBlock` pattern). Pending fetch maps prevent duplicate in-flight requests. Vote batches are deduped per-vote (partial forwarding). App-driven fetching: coordinator does not auto-fetch, app issues `FetchLeiosBlock`/`FetchLeiosBlockTxs`/`FetchLeiosVotes` commands. `LeiosBlockTxsOffered` is a separate event from `LeiosBlockOffered` (not collapsed). `FetchLeiosBlockTxs` carries bitmap for selective TX addressing.
- **Priority scheduling**: Mux uses `StrictPriority` scheduler (not `RoundRobin`). Praos protocols always outprioritize Leios to prevent head-of-line blocking. Priority tiers: Handshake (0), ChainSync (1), BlockFetch (2), TxSubmission (3), KeepAlive (4), LeiosFetch (5), LeiosNotify (6), PeerSharing (7). Named constants in `mux::scheduler::priorities`. StrictPriority can starve low-priority protocols under continuous high-priority load; acceptable because real protocol patterns have natural pauses. LeiosFetch range requests do not get elevated priority (CIP-0164 suggests a separate protocol for that; deferred).

### Known issue: coordinator `.send().await` blocking

The coordinator event loop uses `.send().await` on the `network_events` channel (capacity 64) and per-peer `commands` channels (capacity 16). If the application consumer or a peer task stalls, the coordinator loop blocks, stalling all peers. This affects both Praos and Leios handlers equally. Fix would be switching to `try_send()` or increasing channel capacity. Tracked for a future commit.

## Implementation Phases

1. **Phase 1: Mux + Handshake** — COMPLETE. Bearer, mux, codec, protocol framework, handshake (client+server), CLI, 51 tests, live-tested against mainnet, security-audited.
2. **Phase 2: ChainSync / BlockFetch** — COMPLETE. Shared types (Point, Tip, WrappedHeader, BlockBody), ChainSync + BlockFetch + KeepAlive protocols (state machines, CBOR codecs, client + server), persistent chain follower with reconnection, fake server CLI with Poisson block/rollback generation, 109 tests, live-tested against mainnet, security-audited.
3. **Phase 3: Remaining Praos + Multi-Peer** — COMPLETE. TxSubmission + PeerSharing protocols (38 tests). Multi-peer coordinator with all three connection modes (InitiatorOnly, ResponderOnly, Duplex). Mux composite keys `(ProtocolId, u16)` for bidirectional protocol support. ChainStore, server handlers, responder/duplex tasks, accept loop, InjectBlock/InjectRollback commands. `serve` CLI uses coordinator. `multi-follow --listen --duplex`. 172 total tests. Live-tested: duplex against mainnet, local relay chain (serve → multi-follow → follow).
4. **Phase 4: Leios Protocols** — COMPLETE. Phase 4a (LeiosNotify, protocol ID 18) complete. Phase 4b (LeiosFetch, protocol ID 19, bitmap TX addressing) complete. Phase 4c (Shelley+ header parser with Leios extensions, block body parser) complete. Phase 4d (per-peer task integration) complete: `leios_enabled` config flag, `spawn_leios_notify`/`spawn_leios_fetch` client tasks, `serve_leios_notify`/`serve_leios_fetch` server handlers, `LeiosStore` content-addressed store, Leios PeerEvent/PeerCommand/NetworkEvent/NetworkCommand variants, coordinator stub forwarding, wiring in peer_task/responder_task/duplex_task. Phase 4e (coordinator extensions) complete: slot-bounded dedup for EB/TX/vote offers, per-offer peer tracking, RTT-based smart fetch routing for `FetchLeiosBlock`/`FetchLeiosBlockTxs`/`FetchLeiosVotes`, pending fetch dedup and cleanup, separate `LeiosBlockTxsOffered`/`LeiosBlockTxsReceived` events, `leios_dedup_window` config. CLI `--leios` flag on `serve` and `multi-follow` for local end-to-end testing. Phase 4f (priority scheduling) complete: switched mux from `RoundRobin` to `StrictPriority` scheduler, fixed priority assignments (KeepAlive above Leios, LeiosFetch above LeiosNotify, PeerSharing consistently lowest), added `mux::scheduler::priorities` named constants. 258 total tests.

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
