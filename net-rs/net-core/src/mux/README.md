# mux — Multiplexer

All Cardano mini-protocols share a single TCP connection via this multiplexer. Each protocol gets its own egress queue; the pluggable scheduler decides which to service next. The demuxer routes inbound segments to the correct protocol by composite key.

## Files

| File | Description |
|------|-------------|
| `mod.rs` | `Mux` orchestration — protocol registration, `run()` to start egress/ingress tasks |
| `wire.rs` | 8-byte segment wire format (timestamp, mode+protocol, payload length) |
| `codec.rs` | CBOR framing: `CodecSend` (encode + send) and `CodecRecv` (receive + incremental decode) |
| `scheduler/` | `Scheduler` trait + implementations: `PriorityWfq` (default), `StrictPriority`, `RoundRobin` |
| `channel.rs` | Per-protocol channel halves: `ChannelSend`, `ChannelRecv`, `IngressCounter` |
| `egress.rs` | Muxer task — pulls from protocol queues via scheduler, segments into SDUs, writes to bearer |
| `ingress.rs` | Demuxer task — reads segments from bearer, routes by composite key, enforces buffer limits |

## Wire Format

```
┌──────────────┬─────────────────────────┬────────────────┐
│ Timestamp    │ Mode(1) + Protocol(15)  │ Payload Length  │
│ 4 bytes      │ 2 bytes                 │ 2 bytes         │
└──────────────┴─────────────────────────┴────────────────┘
```

- **Timestamp**: lower 32 bits of monotonic clock (1us resolution)
- **Mode**: 0 = initiator, 1 = responder
- **Protocol**: 15-bit protocol ID (0..32767)
- **Payload**: up to SDU size (default 12,288 bytes per Cardano spec)

## Pluggable Schedulers

The `Scheduler` trait controls egress queue servicing order:

```rust
trait Scheduler: Send + 'static {
    fn register(&mut self, id: ProtocolId, priority: u8);
    fn next(&mut self, ready: &[ProtocolId]) -> Option<ProtocolId>;
}
```

| Scheduler | Description |
|-----------|-------------|
| `PriorityWfq` | **Default.** Two-class: Priority class (Praos) always serviced first; Default class (Leios/PeerSharing) uses message-based weighted fair queuing |
| `StrictPriority` | Hardwired tiers by protocol ID. Can starve low-priority protocols |
| `RoundRobin` | Cycles through ready queues. Ignores traffic class. For testing |

### Traffic Classes

`PriorityWfq` assigns each protocol to a traffic class via `ProtocolConfig`:

| Class | Protocols | Behavior |
|-------|-----------|----------|
| **Priority** | Handshake, ChainSync, BlockFetch, TxSubmission, KeepAlive | Always serviced first, round-robin among ready |
| **Default** (weight=1) | LeiosFetch, LeiosNotify, PeerSharing | WFQ proportional to weight, only when no Priority protocol has data |

Per-protocol traffic class is configurable via `--protocol-priority <id>,<P|weight>` CLI flag.

### StrictPriority Assignments

Named constants in `mux::scheduler::priorities` (used by `StrictPriority` scheduler):

| Priority | Protocol |
|----------|----------|
| 0 | Handshake |
| 1 | ChainSync |
| 2 | BlockFetch |
| 3 | TxSubmission |
| 4 | KeepAlive |
| 5 | LeiosFetch |
| 6 | LeiosNotify |
| 7 | PeerSharing |

## CBOR Codec

- **`CodecSend`**: encodes message via `minicbor::Encode<()>`, sends resulting bytes to channel
- **`CodecRecv`**: reads bytes from channel, incrementally decodes via `minicbor::Decode<'a, ()>`. Uses `for<'a> Decode<'a>` (HRTB) so decoded types are owned, avoiding borrow conflicts. Max buffer 2.5MB (matching BlockFetch StStreaming limit)

## Key Design

- **Non-blocking demuxer**: uses `try_send()` so a slow/malicious protocol never stalls others
- **Ingress accounting**: shared `Arc<AtomicUsize>` between demuxer and `ChannelRecv` for accurate buffer tracking; decremented when protocol consumes data
- **Composite routing keys**: `(ProtocolId, u16)` composite `ChannelKey` enables both initiator and responder directions per protocol on duplex connections
- **SDU timeout**: configurable per-connection timeout for reading segments (default 30s)
- **Buffer limits**: per-protocol ingress limits; exceeding returns `IngressOverflow` error
