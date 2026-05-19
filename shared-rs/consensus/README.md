# shared-consensus

Sans-IO Cardano consensus core. The protocol pieces every
Cardano-Leios implementation must agree on, packaged as a single crate
with no networking, clock, or async runtime — so multiple consumers
(production node, deterministic simulator, fuzzers) can share one
implementation.

## What's in here

| Module          | Responsibility                                                  |
|-----------------|------------------------------------------------------------------|
| `types`         | `Point`, `Tip` with minicbor codec                               |
| `peer`          | `PeerId(u64)` newtype                                            |
| `config`        | `CommitteeSelection` enum (WfaLs / EveryoneVotes / StakeCentile) |
| `pipeline`      | EB lifecycle phases (Voting → CertEligible → expiry)             |
| `wfa`           | Weighted Fait Accompli + Local Sortition committee selection     |
| `aggregation`   | Per-EB vote tally, quorum detection                              |
| `chain_tree`    | In-memory chain DAG, best-tip selection, prune-below-k           |
| `peer_chain`    | Per-peer announced fragment (cap-bounded VecDeque)               |
| `elections`     | Per-EB election state machine; slot ticks → `SlotEffect`         |
| `praos`         | Praos longest-chain state + selection → `PraosEffect`            |
| `leios`         | Linear Leios voting + EB-tx fetch state → `LeiosEffect`          |

The two big state machines are `PraosState` and `LeiosState`. Each
owns its own state, accepts injected `Instant` for time-sensitive
methods, and returns a `Vec<Effect>` describing actions for the caller
to dispatch.

## Architecture

```mermaid
graph TD
    subgraph IO["I/O wrapper (consumer-side)"]
        Net[Network<br/>ChainSync / BlockFetch / Leios mini-protocols]
        Val[Ledger validator]
        Tel[Telemetry sink]
    end

    subgraph Con["shared-consensus (sans-IO)"]
        Praos["PraosState<br/>chain_tree, block_cache,<br/>peer_chains, in_flight"]
        Leios["LeiosState<br/>elections, eb_tx_hashes,<br/>pending_eb_tx_fetches"]
        Elections["Elections<br/>per-EB voting state"]
        Pipeline[PipelineConfig]
        Wfa[wfa]
        Agg[aggregation]
        ChainTree[chain_tree]
        PeerChain[peer_chain]
        Types["types: Point, Tip<br/>peer: PeerId"]
    end

    Net -- "on_block_received,<br/>on_tip_advanced,<br/>on_eb_offered, …" --> Praos
    Net -- "on_eb_received,<br/>on_validated_votes, …" --> Leios
    Praos -- "PraosEffect::FetchBlockRange,<br/>InjectBlock, ValidatorApply, …" --> Net
    Praos -- "ValidatorApply, ValidatorRollback" --> Val
    Leios -- "LeiosEffect::FetchLeiosBlock,<br/>EmitVote, ValidateEb, …" --> Net
    Leios -- "ValidateEb, ValidateVotes" --> Val
    Leios -- "EmitTelemetry" --> Tel

    Leios --> Elections
    Elections --> Agg
    Elections --> Pipeline
    Elections --> Wfa
    Praos --> ChainTree
    Praos --> PeerChain
    Praos --> Types
    Leios --> Types
    Leios --> Wfa
    PeerChain --> Types
    ChainTree --> Types
```

## Effect-driven flow

Both state machines are pure functions of their state plus the input
event. They never call out — the caller drains effects after each
method:

```mermaid
sequenceDiagram
    participant Net as I/O wrapper
    participant Praos as PraosState
    participant Val as Ledger validator

    Net->>Praos: on_block_received(point, header, body, parsed)
    Praos->>Praos: cache, try fork-switch
    Praos-->>Net: [ValidatorApply { … }]
    Net->>Val: dispatch ValidatorApply
    Val-->>Net: ApplyResult::Success
    Net->>Praos: on_block_applied(point, now)
    Praos->>Praos: validate, prune, re-evaluate peers
    Praos-->>Net: [InjectBlock { … }, FetchBlockRange { … }]
    Net->>Net: dispatch each effect
```

The same pattern drives Leios voting:

```mermaid
sequenceDiagram
    participant Net as I/O wrapper
    participant Leios as LeiosState
    participant Elections

    Net->>Leios: on_slot(slot)
    Leios->>Elections: on_slot(slot)
    Elections-->>Leios: [EligibleToVote { eb_hash, eb_slot }]
    Leios->>Leios: decide_vote (PV? NPV?)
    Leios-->>Net: [EmitVote { emit_pv, npv_signature }]
    Net->>Net: build wire vote body, send

    Net->>Leios: on_validated_votes(decoded)
    Leios->>Elections: record_vote (per body)
    Elections-->>Leios: QuorumFormed
    Leios-->>Net: [EmitTelemetry(QuorumReached)]
```

## Praos state machine — events and effects

```mermaid
graph LR
    subgraph events["Public methods (events in)"]
        E1["record_peer_tip /<br/>on_tip_advanced"]
        E2[on_block_received]
        E3[on_block_applied]
        E4[on_block_apply_failed]
        E5[on_block_rolled_back]
        E6[register_self_produced]
        E7[on_peer_disconnected]
        E8[retry_select_chain]
    end

    subgraph fx["PraosEffect (effects out)"]
        F1[FetchBlockRange]
        F2[ReIntersect]
        F3[InjectBlock]
        F4[InjectRollback]
        F5[ValidatorApply]
        F6[ValidatorRollback]
    end

    E1 --> F1
    E1 --> F2
    E1 --> F5
    E2 --> F5
    E2 --> F6
    E3 --> F3
    E3 --> F1
    E5 --> F4
    E6 --> F5
    E8 --> F1
```

## Leios state machine — events and effects

```mermaid
graph LR
    subgraph events["Public methods (events in)"]
        L1[on_slot]
        L2[on_eb_offered]
        L3[on_eb_received]
        L4[on_eb_txs_offered]
        L5[on_eb_txs_received]
        L6[on_votes_offered]
        L7[on_votes_received]
        L8[on_validated_eb]
        L9[on_validated_votes]
        L10[retry_eb_tx_fetch]
    end

    subgraph fx["LeiosEffect (effects out)"]
        E1[FetchLeiosBlock]
        E2[FetchLeiosBlockTxs]
        E3[FetchLeiosVotes]
        E4[RecordLeiosEbManifest]
        E5[EmitVote]
        E6[ValidateEb]
        E7[ValidateVotes]
        E8[EmitTelemetry]
    end

    L1 --> E5
    L1 --> E8
    L2 --> E1
    L3 --> E4
    L3 --> E6
    L4 --> E2
    L6 --> E3
    L7 --> E7
    L9 --> E8
    L10 --> E2
```

## Determinism

`sim-rs` replays whole runs from a seed; shared-consensus must not
introduce non-determinism. The constraints:

- All iteration is over `BTreeMap` / `BTreeSet`. No `HashMap` iteration
  in hot paths.
- Effect ordering is part of the contract: e.g., `Elections::on_slot`
  emits all `EligibleToVote` (sorted by `eb_hash`) before any
  `Expired`.
- Time enters as `Instant` parameters, never `Instant::now()`.
- Randomness flows through `wfa.rs` helpers seeded by stable bytes
  (EB hash, voter id) — there is no `thread_rng` or `from_entropy`
  call anywhere in the crate.

## Module dependencies

```mermaid
graph TD
    leios --> elections
    leios --> wfa
    leios --> pipeline
    leios --> aggregation
    leios --> types
    praos --> chain_tree
    praos --> peer_chain
    praos --> peer
    praos --> types
    elections --> aggregation
    elections --> pipeline
    elections --> wfa
    elections --> config
    aggregation --> pipeline
    chain_tree --> types
    peer_chain --> types
    pipeline --> config
    wfa --> config
```

Nothing in shared-consensus depends on `tokio`, `hyper`, or any
networking crate.

## Building and testing

```sh
cargo build
cargo test
cargo clippy --all-targets -- -D warnings
```

Test layout: every module has its own `#[cfg(test)] mod tests` block.
There are no integration tests — the effect-emission API makes every
scenario directly mockable from a unit test (construct state, drive
events, assert on returned `Vec<Effect>`).

## Consumer integration

A consumer wraps each state machine with an async I/O layer that:

1. Receives wire-format messages from the network and translates them
   into logical args (parsed header info, decoded vote bodies).
2. Calls the appropriate `on_*` method on `PraosState` / `LeiosState`.
3. Drains the returned `Vec<Effect>` and dispatches each variant to
   the right channel — block fetch coordinator, ledger validator,
   telemetry sink, etc.
4. Owns the `Instant` clock; passes `Instant::now()` into methods
   that need it.

See the consumer crates for example wrappers.
