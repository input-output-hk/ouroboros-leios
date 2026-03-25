# bearer — Transport Abstraction

Trait-based transport layer providing pluggable network backends. The `Bearer` trait abstracts over any bidirectional byte stream, allowing protocol and mux code to be transport-agnostic.

## Files

| File | Description |
|------|-------------|
| `mod.rs` | `Bearer` trait definition |
| `tcp.rs` | `TcpBearer` — production TCP transport |
| `mem.rs` | `MemBearer` — in-memory transport for testing |

## Bearer Trait

```rust
trait Bearer: Send + 'static {
    type Read: AsyncRead + Unpin + Send;
    type Write: AsyncWrite + Unpin + Send;

    fn split(self) -> (Self::Read, Self::Write);
}
```

Splits into independent read/write halves for concurrent use by the mux egress and ingress tasks.

## Implementations

| Type | Description |
|------|-------------|
| `TcpBearer` | Wraps `tokio::net::TcpStream`. Sets `TCP_NODELAY` for low latency. Methods: `connect(addr)`, `connect_timeout(addr, timeout)`, `accept(listener)` |
| `MemBearer` | In-memory duplex stream for unit/integration testing. `pair()` creates two connected endpoints with 128KB buffer (matching Haskell). `pair_with_buffer(size)` for custom buffer sizes |

## Extending

To add a new transport (QUIC, Unix sockets, etc.), implement `Bearer` for your type. No changes needed to mux or protocol code.
