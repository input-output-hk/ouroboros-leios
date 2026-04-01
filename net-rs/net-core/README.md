# net-core

Library crate implementing the Cardano node-to-node (N2N) network stack. Provides all protocol logic, multiplexing, transport abstraction, and multi-peer coordination for both Praos and Leios (CIP-0164).

## Module Structure

```
src/
├── lib.rs
├── bearer/           # Transport abstraction (pluggable backends)
├── mux/              # Multiplexer (wire format, scheduling, codec)
├── types/            # Shared Cardano types (Point, Tip, Header, Block)
├── protocols/        # All 8 mini-protocols (state machines + CBOR)
├── store/            # Shared data stores (ChainStore, LeiosStore)
├── peer/             # Per-peer tasks, server handlers
└── multi_peer/       # Multi-peer coordinator, application interface
```

## Modules

| Module | Description | README |
|--------|-------------|--------|
| **bearer** | `Bearer` trait + `TcpBearer` / `MemBearer` implementations | [bearer/](src/bearer/) |
| **mux** | Multiplexer with pluggable schedulers (`PriorityWfq` default, `StrictPriority`, `RoundRobin`), wire format, CBOR codec, non-blocking demuxer | [mux/](src/mux/) |
| **types** | `Point`, `Tip`, `WrappedHeader`, `HeaderInfo`, `BlockBody`, `LeiosBlockInfo` | [types/](src/types/) |
| **protocols** | Protocol framework (`Protocol` trait, `Runner`) + all 8 mini-protocols with state machines and agency tables | [protocols/](src/protocols/) |
| **store** | `ChainStore` (linear chain state), `LeiosStore` (content-addressed Leios data) — shared between coordinator and server handlers | [store/](src/store/) |
| **peer** | Per-peer tasks (initiator/responder/duplex), server-side protocol handlers, connection setup | [peer/](src/peer/) |
| **multi_peer** | Multi-peer coordinator, tip dedup, fetch routing, application interface (`NetworkEvent`/`NetworkCommand`) | [multi_peer/](src/multi_peer/) |

## Layer Diagram

```
┌─────────────────────────────────────────────┐
│  multi_peer/  Coordinator, app interface    │
├─────────────────────────────────────────────┤
│  peer/        Per-peer tasks, handlers      │
├─────────────────────────────────────────────┤
│  protocols/   8 mini-protocols (via Runner) │
├─────────────────────────────────────────────┤
│  mux/         Multiplexer + CBOR codec      │
├─────────────────────────────────────────────┤
│  bearer/      Transport (TCP / memory)      │
└─────────────────────────────────────────────┘
  store/  shared between multi_peer and peer
  types/  shared across all layers
```
