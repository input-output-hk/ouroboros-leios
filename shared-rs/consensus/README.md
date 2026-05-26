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
| `committee`     | Committee selection (WfaLs, EveryoneVotes, StakeCentile), NPV lottery |
| `lottery`       | Praos f_block stake-weighted threshold formula                   |
| `aggregation`   | Per-EB vote tally, quorum detection                              |
| `bitmap`        | Sparse `BTreeMap<u16, u64>` for `MsgLeiosBlockTxsRequest`        |
| `chain_tree`    | In-memory chain DAG, best-tip selection, prune-below-k           |
| `peer_chain`    | Per-peer announced fragment (cap-bounded VecDeque)               |
| `fetch`         | Pluggable per-channel fetch policies + candidate tracker         |
| `elections`     | Per-EB election state machine; slot ticks → `SlotEffect`         |
| `praos`         | Praos longest-chain state + selection → `PraosEffect`            |
| `leios`         | Linear Leios voting + EB-tx fetch state → `LeiosEffect`          |
| `mempool`       | Bounded tx pool + EB-pinned bodies → `MempoolEffect`             |
| `production`    | Producer-side body-path picker (inline / EB / empty-for-safety)  |
| `behaviour`     | Pluggable per-node hooks for adversarial / experimental variants |

The three big state machines are `PraosState`, `LeiosState` and
`MempoolState`. Each owns its own state, accepts injected `Instant` for
time-sensitive methods, and returns a `Vec<Effect>` describing actions
for the caller to dispatch. See [`src/behaviour/README.md`](src/behaviour/README.md)
for the per-node hook system that lets consumers slot adversarial
variants into any of the three without forking the honest control flow.

## Architecture

```mermaid
graph TD
    subgraph IO["I/O wrapper (consumer-side)"]
        Net[Network<br/>ChainSync / BlockFetch / Leios / TxSubmission]
        Val[Ledger / tx validator]
        Tel[Telemetry sink]
    end

    subgraph Con["shared-consensus (sans-IO)"]
        Praos["PraosState<br/>chain_tree, block_cache,<br/>peer_chains, in_flight,<br/>equivocating_rb_slots"]
        Leios["LeiosState<br/>elections, eb_tx_hashes,<br/>pending_eb_tx_fetches"]
        Mempool["MempoolState<br/>txs, tx_index,<br/>eb_manifests, eb_pinned"]
        Behaviour["behaviour<br/>Arc&lt;Mutex&lt;dyn Behaviour&gt;&gt;"]
        Production[production: BodyPath]
        Elections["Elections<br/>per-EB voting state"]
        Pipeline[PipelineConfig]
        Committee[committee]
        Lottery[lottery]
        Agg[aggregation]
        ChainTree[chain_tree]
        PeerChain[peer_chain]
        Fetch[fetch]
        Bitmap[bitmap]
        Types["types: Point, Tip<br/>peer: PeerId"]
    end

    Net -- "on_block_received,<br/>on_tip_advanced, …" --> Praos
    Net -- "on_eb_offered,<br/>on_validated_votes, …" --> Leios
    Net -- "on_tx_received,<br/>on_tx_validated" --> Mempool
    Praos -- "FetchBlockRange, InjectBlock,<br/>ValidatorApply, …" --> Net
    Praos -- "ValidatorApply, ValidatorRollback" --> Val
    Leios -- "FetchLeiosBlock, EmitVote,<br/>ValidateEb, …" --> Net
    Leios -- "ValidateEb, ValidateVotes" --> Val
    Mempool -- "ValidateTx" --> Val
    Mempool -- "TxRejected" --> Tel
    Leios -- "EmitTelemetry" --> Tel

    Behaviour -. "consulted at every<br/>protocol-affecting decision" .-> Praos
    Behaviour -. " " .-> Leios
    Behaviour -. " " .-> Mempool

    Leios --> Elections
    Leios --> Fetch
    Elections --> Agg
    Elections --> Pipeline
    Elections --> Wfa
    Praos --> ChainTree
    Praos --> PeerChain
    Praos --> Fetch
    Praos --> Lottery
    Production --> Leios
    Production --> Mempool
    Fetch --> Bitmap
    PeerChain --> Types
    ChainTree --> Types
```

## Effect-driven flow

Each state machine is a pure function of its state plus the input
event. They never call out — the caller drains effects after each
method, dispatches them, and feeds outcomes back in. The four major
event flows below cover transactions, RBs, EBs, and votes.

### Transactions — admit, advertise, drain

The mempool moves a tx through validate → admit → advertise on the
inbound side, then drains it into an RB body (or an EB manifest) on
the producer side.

```mermaid
sequenceDiagram
    participant Net as I/O wrapper
    participant Mp as MempoolState
    participant Val as Tx validator
    participant Prod as Producer loop

    Note over Net,Mp: Inbound from a peer
    Net->>Mp: on_tx_received(tx_id, body)
    Mp-->>Net: [ValidateTx { tx_id, body }]
    Net->>Val: dispatch ValidateTx
    Val-->>Net: ValidatedTx { size } / Failed
    alt validated
        Net->>Mp: on_tx_validated(tx_id, size)
        Mp->>Mp: admit, evict-oldest if full
        Mp-->>Net: [] (possibly TxRejected{QueueFull} for evicted)
        Net->>Mp: peek_unannounced_for_peer(peer, ...)
        Mp-->>Net: tx ids to push via TxSubmission
    else rejected
        Net->>Mp: on_tx_validation_failed(tx_id, reason)
        Mp-->>Net: [TxRejected { ValidationFailed }]
    end

    Note over Prod,Mp: Producer drains for RB body
    Prod->>Mp: drain_up_to(rb_body_max_bytes) / drain_all
    Mp-->>Prod: Vec<PendingTx>
    Note right of Prod: Or on overflow:<br/>production::BodyPath::decide<br/>returns Eb { manifest }
    Prod->>Mp: produce_eb(eb_key, manifest) [pins bodies]
```

### Ranking Blocks — header → fetch → validate → adopt

```mermaid
sequenceDiagram
    participant Net as I/O wrapper
    participant Praos as PraosState
    participant Val as Ledger validator
    participant Mp as MempoolState

    Net->>Praos: record_peer_tip(peer, tip)
    Praos->>Praos: note header equivocation, update peer_chain
    Praos-->>Net: [FetchBlockRange { from, to, peers }, ReIntersect, …]
    Net->>Net: dispatch BlockFetch to chosen peers

    Net->>Praos: on_block_received(point, header, body, parsed)
    Praos->>Praos: cache, try fork-switch
    Praos-->>Net: [ValidatorApply { point, body, prev_hash }]
    Net->>Val: dispatch ValidatorApply
    Val-->>Net: ApplyResult::Success

    Net->>Praos: on_block_applied(point, now)
    Praos->>Praos: mark validated, prune-below-k, re-select
    Praos-->>Net: [InjectBlock, FetchBlockRange, ValidatorApply, …]
    Net->>Mp: on_block_applied(included_tx_ids) [drop from mempool]
```

Producer side: when this node wins the slot lottery
(see `lottery::rb_win_threshold`), the wrapper consults
`Behaviour::rb_production_strategy`, decides the body path via
`production::BodyPath::decide`, and calls
`Praos::register_self_produced` — which routes through the same
validation pipeline so self-produced blocks land in the chain on the
same on_block_applied path.

### Endorser Blocks — offer → fetch → validate → endorse

EB diffusion is two-stage: the wrapper fetches the EB **body** (the
ordered tx-hash manifest), then fans out per-tx fetches for the
bodies it doesn't already hold.

```mermaid
sequenceDiagram
    participant Net as I/O wrapper
    participant Leios as LeiosState
    participant Val as EB validator
    participant Mp as MempoolState

    Net->>Leios: on_eb_offered(point, peer)
    Leios->>Leios: candidate tracker, dedup against pending fetches
    Leios-->>Net: [FetchLeiosBlock { point, peers }]
    Net->>Net: dispatch leios-fetch to chosen peers

    Net->>Leios: on_eb_received(point, tx_hashes)
    Leios-->>Net: [RecordLeiosEbManifest, ValidateEb]
    Net->>Val: dispatch ValidateEb
    Val-->>Net: validated
    Net->>Leios: on_validated_eb(point)
    Net->>Mp: record_eb_manifest(eb_key, manifest)

    Note over Net,Leios: Wrapper drives EB-tx fetch
    Net->>Leios: missing_eb_tx_bitmap(eb_hash, mempool)
    Leios-->>Net: BTreeMap<u16, u64> (missing indices)
    Net->>Leios: on_eb_txs_offered(point, peer, bitmap)
    Leios-->>Net: [FetchLeiosBlockTxs { point, bitmap, peers }]
    Net->>Leios: on_eb_txs_received(point, count)
    Note over Leios: After all closure txs land,<br/>the local vote predicate<br/>can clear MissingTX

    Note over Net,Leios: Later, when a child RB cert lands
    Net->>Leios: on_chain_endorsement(eb_slot, eb_hash)
    Leios->>Leios: clear endorsed_unvalidated_ebs<br/>once locally validated
```

### Votes — election → emit → diffuse → quorum

```mermaid
sequenceDiagram
    participant Net as I/O wrapper
    participant Leios as LeiosState
    participant El as Elections
    participant Beh as Behaviour
    participant Agg as aggregation
    participant Val as Vote validator

    Note over Net,Leios: Outbound — self voting
    Net->>Leios: on_slot(slot, tx_known)
    Leios->>El: on_slot(slot)
    El-->>Leios: [EligibleToVote { eb_hash, eb_slot }, …]
    Leios->>Leios: decide_vote (honest predicate)
    Leios->>Beh: decide_vote(honest)
    Beh-->>Leios: Continue / Override(reason)
    alt vote
        Leios->>El: mark_voted(eb_hash)
        Leios-->>Net: [EmitVote { emit_pv, npv_signature }]
        Note right of Net: Wrapper builds wire vote body,<br/>signs, ships via Leios-fetch
    else abstain
        Leios-->>Net: [NoVote { reason }, EmitTelemetry]
    end
    El-->>Leios: [Expired { eb_slot }] (at window end)
    Leios-->>Net: [EmitTelemetry(ElectionExpired)]

    Note over Net,Leios: Inbound — gossiped votes
    Net->>Leios: on_votes_offered(peer, vote_ids)
    Leios-->>Net: [FetchLeiosVotes { per_peer }]
    Net->>Leios: on_votes_received(vote_ids, vote_data)
    Leios-->>Net: [ValidateVotes]
    Net->>Val: dispatch ValidateVotes
    Val-->>Net: validated
    Net->>Leios: on_validated_votes(decoded)
    Leios->>Agg: record_vote (per body)
    Agg-->>Leios: Inserted / QuorumFormed
    Leios-->>Net: [EmitTelemetry(QuorumReached)]
```

## Praos state machine — events and effects

```mermaid
graph LR
    subgraph events["Public methods (events in)"]
        E1[record_peer_tip /<br/>on_tip_advanced]
        E2[on_block_received]
        E3[on_block_applied]
        E4[on_block_apply_failed]
        E5[on_block_rolled_back]
        E6[register_self_produced]
        E7[on_peer_disconnected]
        E8[on_peer_rolled_back]
        E9[on_block_fetch_failed]
        E10[retry_select_chain]
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
    E10 --> F1
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
        L10[on_chain_endorsement]
        L11[retry_eb_tx_fetch]
    end

    subgraph fx["LeiosEffect (effects out)"]
        E1[FetchLeiosBlock]
        E2[FetchLeiosBlockTxs]
        E3[FetchLeiosVotes]
        E4[RecordLeiosEbManifest]
        E5[EmitVote]
        E6[NoVote]
        E7[ValidateEb]
        E8[ValidateVotes]
        E9[EmitTelemetry]
    end

    L1 --> E5
    L1 --> E6
    L1 --> E9
    L2 --> E1
    L3 --> E4
    L3 --> E7
    L4 --> E2
    L6 --> E3
    L7 --> E8
    L9 --> E9
    L11 --> E2
```

## Mempool state machine — events and effects

```mermaid
graph LR
    subgraph events["Public methods (events in)"]
        M1[on_tx_received]
        M2[on_tx_validated]
        M3[on_tx_validation_failed]
        M4[admit_validated]
        M5[on_block_applied]
        M6[record_eb_manifest]
        M7[produce_eb]
        M8[merge_eb_body]
    end

    subgraph fx["MempoolEffect (effects out)"]
        N1[ValidateTx]
        N2[TxRejected]
    end

    M1 --> N1
    M1 --> N2
    M2 --> N2
    M3 --> N2
    M4 --> N2
    M6 --> N2
    M7 --> N2
```

## Behaviour hooks

`PraosState`, `LeiosState`, and `MempoolState` each own a
`BehaviourHandle = Arc<Mutex<Box<dyn Behaviour>>>`. Every
protocol-affecting decision consults the behaviour first: reactive
hooks (`on_*`) can `Continue`, `Replace`, or `Append` effects; decision
hooks (`decide_vote`, `decide_body_path`) can override the honest
choice; strategy hooks (`rb_production_strategy`) tell the wrapper to
suppress or equivocate. A separate per-peer outbound transform path
([`Behaviour::transform_outbound`]) lets a behaviour drop or rewrite an
artefact differently for each peer it goes out to — the basis for
peer-split equivocation and eclipse simulations.

Behaviours are deserialised from config via the
`BehaviourSpec` enum (`kind = "honest"`, `"lazy-voter"`,
`"rb-header-equivocator"`, `"composite"`), seeded from the per-node id,
and composable. The honest default is a no-op; concrete behaviours
override only what they need.

See [`src/behaviour/README.md`](src/behaviour/README.md) for the full
trait surface, dispatch rules, registry, and the recipe for shipping a
new behaviour.

## Fetch policies

Each fetch channel (Praos block fetch, Leios EB fetch, Leios EB-tx
fetch, Leios vote fetch) has its own policy trait in
[`fetch`](src/fetch.rs). Stock implementations:

- `LowestRttFirst` — pick the single peer with the lowest measured RTT.
- `BroadcastN` — fan a fetch out to the N best peers.

RTT lookup is a borrowed `PeerRtt` handle passed at call time; the
shared `PeerRttCache` carries live measurements between the wrapper's
KeepAlive handler and the state machines. Candidate-peer sets and
in-flight dedup live in `CandidateTracker`, fed by the wrapper's
`note_*_offered` calls when it observes an offer on the wire.

## Determinism

`sim-rs` replays whole runs from a seed; shared-consensus must not
introduce non-determinism. The constraints:

- All iteration is over `BTreeMap` / `BTreeSet`. No `HashMap` iteration
  in hot paths.
- Effect ordering is part of the contract: e.g., `Elections::on_slot`
  emits all `EligibleToVote` (sorted by `eb_hash`) before any
  `Expired`.
- Time enters as `Instant` parameters, never `Instant::now()`.
- Randomness flows through `committee.rs` and `lottery.rs` helpers seeded by
  stable bytes (EB hash, voter id, stake) — there is no `thread_rng`
  or `from_entropy` call anywhere in the crate.
- Behaviours follow the same rules: they take a seed at construction
  and hash it with the per-decision key (peer id, slot, …).

## Module dependencies

```mermaid
graph TD
    leios --> elections
    leios --> committee
    leios --> pipeline
    leios --> aggregation
    leios --> fetch
    leios --> behaviour
    leios --> types
    praos --> chain_tree
    praos --> peer_chain
    praos --> peer
    praos --> fetch
    praos --> lottery
    praos --> behaviour
    praos --> types
    mempool --> behaviour
    mempool --> peer
    production --> leios
    production --> mempool
    elections --> aggregation
    elections --> pipeline
    elections --> committee
    elections --> config
    aggregation --> pipeline
    chain_tree --> types
    peer_chain --> types
    pipeline --> config
    committee --> config
    fetch --> bitmap
    fetch --> peer
    fetch --> types
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
2. Calls the appropriate `on_*` method on `PraosState` / `LeiosState`
   / `MempoolState`.
3. Drains the returned `Vec<Effect>` and dispatches each variant to
   the right channel — block fetch coordinator, ledger validator,
   tx validator, telemetry sink, etc.
4. Owns the `Instant` clock; passes `Instant::now()` into methods
   that need it.
5. (Optional) Hands a `BehaviourHandle` to the state machines at
   construction or via `set_behaviour` / `swap_handle`, and calls
   `transform_outbound` on every peer-targeted send so adversarial
   per-peer rewrites stay invisible to the honest dispatch path.

See the consumer crates for example wrappers.

[`Behaviour::transform_outbound`]: src/behaviour/README.md#outbound-transform--per-peer-rewriting
