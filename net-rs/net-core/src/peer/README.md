# peer — Per-Peer Protocol Handling

Manages individual peer connections: connection setup, protocol sub-tasks (initiator, duplex), and server-side handlers. Multi-peer coordination lives in the `multi_peer` module.

## Files

| File | Description |
|------|-------------|
| `mod.rs` | `PeerId`, `ConnectionMode`, `PeerError` |
| `types.rs` | `PeerEvent`, `PeerCommand` (peer ↔ coordinator boundary) |
| `command_dispatch.rs` | Routes `PeerCommand` messages to the right protocol sub-task |
| `connect.rs` | Connection setup helpers: TCP + mux + handshake wiring |
| `peer_task.rs` | Per-peer initiator task: spawns client protocol sub-tasks |
| `duplex_task.rs` | Per-peer duplex task: both client + server on one connection (also used by the accept loop for inbound connections) |
| `server_handlers.rs` | Server-side protocol implementations (ChainSync, BlockFetch, KeepAlive, TxSubmission, PeerSharing, LeiosNotify, LeiosFetch) |

## Connection Modes

| Mode | Description |
|------|-------------|
| `InitiatorOnly` | Outbound connection — runs client protocol sub-tasks (ChainSync, BlockFetch, KeepAlive, etc.) |
| `ResponderOnly` | Reserved — inbound-only peers currently run through `Duplex` via the accept loop |
| `Duplex` | Both client and server protocols on one connection, using composite mux keys for bidirectional routing |

## Per-Peer Task Architecture

Each peer runs an independent tokio task tree.

**Initiator** (`peer_task.rs`) spawns client sub-tasks:
- `spawn_chainsync` — find intersection then continuous request_next loop
- `spawn_blockfetch` — awaits `FetchBlocks` commands, streams blocks
- `spawn_keepalive` — periodic ping at configurable interval
- `spawn_peersharing` — awaits `RequestPeers` commands
- `spawn_leios_notify` — continuous request_next loop (if enabled)
- `spawn_leios_fetch` — awaits `FetchLeios*` commands (if enabled)

**Duplex** (`duplex_task.rs`) registers each protocol twice (once per direction) using `register_with_mode()` and spawns both the client sub-tasks above and the server handlers below. Inbound connections from the coordinator's accept loop are handled as duplex peers.

**Server handlers** (`server_handlers.rs`):
- `serve_chainsync`, `serve_blockfetch`, `serve_txsubmission`, `serve_peersharing`, `serve_keepalive`, `serve_leios_notify`, `serve_leios_fetch`
