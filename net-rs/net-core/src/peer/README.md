# peer — Multi-Peer Coordination

Manages multiple concurrent peer connections with aggregation, deduplication, and smart routing. Provides a peer-agnostic application interface via `NetworkEvent`/`NetworkCommand` channels.

## Files

| File | Description |
|------|-------------|
| `mod.rs` | `PeerId`, `ConnectionMode`, `CoordinatorConfig`, `CoordinatorHandle`, `PeerError` |
| `types.rs` | `PeerEvent`, `PeerCommand`, `NetworkEvent`, `NetworkCommand` |
| `connect.rs` | Connection setup helpers: TCP + mux + handshake wiring |
| `chain_store.rs` | `ChainStore`: thread-safe in-memory chain state with change notifications |
| `leios_store.rs` | `LeiosStore`: content-addressed Leios data store (EBs, TXs, votes) |
| `peer_task.rs` | Per-peer initiator task: spawns client protocol sub-tasks |
| `responder_task.rs` | Per-peer responder task: spawns server protocol handlers |
| `duplex_task.rs` | Per-peer duplex task: both client + server on one connection |
| `server_handlers.rs` | Server-side protocol implementations (ChainSync, BlockFetch, KeepAlive, TxSubmission, PeerSharing, LeiosNotify, LeiosFetch) |
| `coordinator.rs` | Multi-peer aggregation, tip dedup, fetch routing, accept loop, reconnection |

## Connection Modes

| Mode | Description |
|------|-------------|
| `InitiatorOnly` | Outbound connection — runs client protocol sub-tasks (ChainSync, BlockFetch, KeepAlive, etc.) |
| `ResponderOnly` | Inbound connection via accept loop — runs server protocol handlers |
| `Duplex` | Both client and server protocols on one connection, using composite mux keys for bidirectional routing |

## Coordinator

Single tokio task that aggregates all peer events:

- **Tip deduplication**: only forwards `TipAdvanced` when tip actually changes
- **Smart block fetch routing**: picks peer with best RTT for `FetchBlock` commands
- **Accept loop**: listens for inbound connections when `listen_address` is configured
- **Reconnection**: exponential backoff for failed outbound/duplex peers; no reconnection for responders
- **Leios intelligence** (when `leios_enabled`):
  - Slot-bounded seen sets for EB/TX/vote offer deduplication (`leios_dedup_window`, default 1000 slots)
  - Per-offer peer tracking for RTT-based smart fetch routing
  - Pending fetch maps prevent duplicate in-flight requests
  - Vote batches deduped per-vote (partial forwarding)

## Stores

### ChainStore

Thread-safe (`Mutex`) linear chain storage:
- `VecDeque<StoredBlock>` with capacity limit (auto-evicts oldest)
- Change notifications via `watch::channel` for server handlers
- `find_intersection(points)` for ChainSync server
- `append_block`, `rollback_to`, `tip`, `block_at`, `blocks_after`

### LeiosStore

Content-addressed (`Mutex`) storage keyed by `(slot, hash)`:
- Separate maps for blocks, block_txs, votes (opaque bytes)
- Notification queue for LeiosNotify server (`pop_notifications`)
- Change notifications via `watch::channel`
- `inject_block`, `inject_block_txs`, `inject_votes`, `get_block`, `get_votes`

## Application Interface

```
NetworkCommand (app -> coordinator)     NetworkEvent (coordinator -> app)
├── AddPeer { address }                 ├── PeerConnected { peer_id }
├── FetchBlock { point }                ├── PeerDisconnected { peer_id }
├── DiscoverPeers                       ├── TipAdvanced { tip, header }
├── InjectBlock { point, header, body } ├── RolledBack { point, tip }
├── InjectRollback { point }            ├── BlockReceived { point, body }
├── FetchLeiosBlock { slot, hash }      ├── LeiosBlockOffered { slot, hash }
├── FetchLeiosBlockTxs { .. }           ├── LeiosBlockReceived { .. }
├── FetchLeiosVotes { votes }           ├── LeiosVotesReceived { .. }
└── Shutdown                            └── ...
```

`CoordinatorHandle` bundles the two channel endpoints for application use.

## Per-Peer Task Architecture

Each peer runs an independent tokio task tree:

**Initiator** (`peer_task.rs`) spawns sub-tasks:
- `spawn_chainsync` — find intersection then continuous request_next loop
- `spawn_blockfetch` — awaits `FetchBlocks` commands, streams blocks
- `spawn_keepalive` — periodic ping at configurable interval
- `spawn_peersharing` — awaits `RequestPeers` commands
- `spawn_leios_notify` — continuous request_next loop (if enabled)
- `spawn_leios_fetch` — awaits `FetchLeios*` commands (if enabled)

**Responder** (`responder_task.rs`) spawns server handlers:
- `serve_chainsync`, `serve_blockfetch`, `serve_txsubmission`, `serve_peersharing`, `serve_keepalive`, `serve_leios_notify`, `serve_leios_fetch`

**Duplex** (`duplex_task.rs`) combines both, registering each protocol twice (once per direction) using `register_with_mode()`.
