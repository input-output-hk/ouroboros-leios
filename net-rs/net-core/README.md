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
└── peer/             # Multi-peer coordinator, per-peer tasks, stores
```

## Modules

| Module | Description | README |
|--------|-------------|--------|
| **bearer** | `Bearer` trait + `TcpBearer` / `MemBearer` implementations | [bearer/](src/bearer/) |
| **mux** | Multiplexer with pluggable schedulers (`StrictPriority`, `RoundRobin`), wire format, CBOR codec, non-blocking demuxer | [mux/](src/mux/) |
| **types** | `Point`, `Tip`, `WrappedHeader`, `HeaderInfo`, `BlockBody`, `LeiosBlockInfo` | [types/](src/types/) |
| **protocols** | Protocol framework (`Protocol` trait, `Runner`) + all 8 mini-protocols with state machines and agency tables | [protocols/](src/protocols/) |
| **peer** | Multi-peer coordinator, per-peer tasks (initiator/responder/duplex), `ChainStore`, `LeiosStore`, application interface | [peer/](src/peer/) |

## Layer Diagram

```
┌─────────────────────────────────────────────┐
│  peer/        Coordinator, per-peer tasks   │
├─────────────────────────────────────────────┤
│  protocols/   8 mini-protocols (via Runner) │
├─────────────────────────────────────────────┤
│  mux/         Multiplexer + CBOR codec      │
├─────────────────────────────────────────────┤
│  bearer/      Transport (TCP / memory)      │
└─────────────────────────────────────────────┘
        types/  shared across all layers
```
