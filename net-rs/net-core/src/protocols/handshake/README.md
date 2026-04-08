# Handshake (Protocol ID 0)

Version negotiation at connection startup. Client proposes a version table; server accepts one version or refuses. Always the first protocol to run on a new connection.

## Files

| File | Description |
|------|-------------|
| `mod.rs` | State machine (`State`, `Message`), `Protocol` impl, client/server entry points |
| `codec.rs` | CBOR encode/decode for handshake messages |
| `n2n.rs` | N2N version data: `VersionTable`, `VersionData`, magic constants, CBOR codec |

## State Machine

```mermaid
stateDiagram-v2
    [*] --> Propose
    Propose --> Confirm : MsgProposeVersions
    Confirm --> Done : MsgAcceptVersion
    Confirm --> Done : MsgRefuse
    Confirm --> Done : MsgQueryReply
    Done --> [*]
```

## Agency Table

| State | Agency | Message | Next State |
|-------|--------|---------|------------|
| Propose | **Client** | MsgProposeVersions(version_table) | Confirm |
| Confirm | **Server** | MsgAcceptVersion(version, params) | Done |
| Confirm | **Server** | MsgRefuse(reason) | Done |
| Confirm | **Server** | MsgQueryReply(version_table) | Done |
| Done | Nobody | — | — |

## Limits

- **Max message size**: 5,760 bytes
- **Timeout**: 10s (all states)

## Entry Points

- `run_client(codec_send, codec_recv, versions) -> Result<(u64, Vec<u8>)>` — propose versions, return accepted version + params
- `run_server(codec_send, codec_recv, versions) -> Result<(u64, Vec<u8>)>` — receive proposals, accept best match or refuse
