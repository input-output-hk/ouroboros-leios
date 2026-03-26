# multi_peer — Multi-Peer Coordination

Manages multiple concurrent peer connections with aggregation, deduplication, and smart routing. Provides a peer-agnostic application interface via `NetworkEvent`/`NetworkCommand` channels.

## Files

| File | Description |
|------|-------------|
| `mod.rs` | `CoordinatorConfig`, `CoordinatorHandle`, `spawn_coordinator` re-export |
| `types.rs` | `NetworkEvent`, `NetworkCommand` (coordinator ↔ application boundary) |
| `coordinator.rs` | Multi-peer aggregation, tip dedup, fetch routing, accept loop, reconnection |

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

The coordinator creates and populates shared stores (`ChainStore`, `LeiosStore`) from the `store` module; server handlers in `peer` read from them.

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
