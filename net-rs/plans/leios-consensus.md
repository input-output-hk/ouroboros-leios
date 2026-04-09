# Leios Consensus — Next Steps

This document captures the roadmap for building the Leios consensus layer on
top of the existing Praos implementation. The network plumbing (protocols,
store, tracker, coordinator, production stubs) is complete; what follows is
the actual EB/vote/certificate logic plus the wiring that lets Praos see
certified EBs.

Commit `3c7eca140` split `consensus.rs` into `consensus/{mod,praos,leios}.rs`
and moved the offer→fetch routing into `LeiosConsensus`. That module is now
the home for everything below.

## Immediate goal: vote bandwidth measurement

Validate the bandwidth load of the Leios voting mechanism under different
committee selection rules (wFA+LS, EveryoneVotes, StakeCentile). Three
phases of work, each independently useful:

**Phase 1** (in progress): Vote plumbing + structure + committee selection types.
Vote IDs carried through fetch pipeline, fetched votes re-injected for
epidemic flooding, structured fake vote bodies (130-180B), CommitteeSelection
enum with VoteDecision (PersistentVote / NonPersistentVote / NoVote).

### Phase 2: EB-triggered voting with committee selection

Votes become reactive to EBs. Committee selection gates who votes.

**`net-node/src/consensus/leios.rs`** — expand `LeiosConsensus` with:
- `rng: StdRng`
- `stake: u64, total_stake: u64`
- `committee_selection: CommitteeSelection`
- `persistent_vote_bytes: usize, non_persistent_vote_bytes: usize`
- `stage_length_slots: u64`
- `dyn_config: watch::Receiver<DynamicConfig>` (for `vote_generation_probability`)
- `voted_ebs: HashSet<[u8; 32]>` — prevent double-voting on same EB

New method `try_vote_on_eb(&mut self, eb_point: &Point)`:
1. Extract hash from `Point::Specific`; skip if in `voted_ebs`
2. Compute `election_id` from slot (slot / stage_length_slots)
3. Read `vote_generation_probability` from `dyn_config`
4. Call `committee_selection.decide_vote(stake, total_stake, vote_prob, &mut rng)`
5. Match on `VoteDecision`:
   - `NoVote` → return
   - `PersistentVote` → vote_bytes = persistent_vote_bytes, tag = 0
   - `NonPersistentVote` → vote_bytes = non_persistent_vote_bytes, tag = 1
6. Build vote_id = `(slot, node_id_hash_bytes)`
7. Build vote body via `build_fake_vote_body(tag, election_id, node_id, &eb_hash, vote_bytes)`
8. Send `NetworkCommand::InjectLeiosVotes { votes: vec![vote_id], data: vec![body] }`
9. Insert eb_hash into `voted_ebs`
10. Buffer a `LeiosEvent::VoteProduced` for telemetry (includes vote_type + size)

In `handle_event(LeiosBlockReceived { point, .. })`:
- Call `self.try_vote_on_eb(&point)` after existing logging

**`net-node/src/consensus/mod.rs`** — update `Consensus::new` to accept
committee selection config + dyn_config, forward to `LeiosConsensus`.

**`net-node/src/main.rs`**:
- Pass config to `Consensus::new`
- **Remove** the `try_produce_votes()` block (~lines 163-174)
- Keep EB production at stage boundaries unchanged

**`net-node/src/production.rs`**:
- Remove `try_produce_votes()`, `ProducedVotes`, `vote_count`
- Keep `build_fake_vote_body` as a public utility function

**Tests (write first)**:
- `vote_produced_on_eb_received_everyone`: EveryoneVotes + LeiosBlockReceived
  → InjectLeiosVotes on channel with correct payload size
- `no_vote_zero_stake`: stake=0 → no vote
- `no_vote_low_centile`: StakeCentile(0.1), expect most nodes excluded
- `vote_high_centile`: StakeCentile(0.95), expect most nodes included
- `no_double_vote_same_eb`: same EB twice → one vote
- `vote_body_references_correct_eb`: parse vote body, verify EB hash matches

**Observable after**: Cluster with `committee_selection = "EveryoneVotes"`,
`leios_enabled = true`: EB produced → all staked nodes receive it → each
checks committee membership → selected nodes produce ~130-180B votes →
votes flood via LeiosNotify/LeiosFetch → other nodes re-serve them.

### Phase 3: Quorum detection + bandwidth stats

Track votes per EB, detect quorum, emit telemetry for bandwidth analysis.

**Vote aggregation in `net-node/src/consensus/leios.rs`**:

```rust
struct EbVoteTally {
    eb_point: Point,
    stage: u64,
    voters: HashSet<Vec<u8>>,    // unique voter node IDs (parsed from vote body)
    quorum_reached: bool,
    first_vote_at: Instant,
    quorum_at: Option<Instant>,
}
```

Add to `LeiosConsensus`:
- `tallies: HashMap<[u8; 32], EbVoteTally>` — keyed by EB hash
- `votes_produced: u64, votes_received: u64, vote_bytes_received: u64`
- `quorums_formed: u64`

On `LeiosVotesReceived { ids, votes }`: for each vote blob:
1. Parse to extract `endorser_block_hash` and `voter_node_id`
2. Find or create `EbVoteTally` for that EB
3. Insert voter into `voters` set (dedup)
4. Estimate stake: `voters.len() * (total_stake / num_expected_nodes)`
5. If crosses `quorum_stake_fraction`: set quorum, emit `QuorumReached` event
6. Increment `vote_bytes_received += blob.len()`

Own votes counted in tally when produced (Phase 2's `try_vote_on_eb`).
Prune tallies older than `leios_dedup_window` slots.

**Telemetry in `net-node/src/telemetry.rs`** — new `NodeEvent` variants:
- `VoteProduced { node, slot, eb_hash_hex, payload_bytes }`
- `QuorumReached { node, slot, eb_hash_hex, vote_count, time_to_quorum_ms }`
- `LeiosStats { node, votes_produced, votes_received, vote_bytes_received, quorums_formed }`

**Cluster config**:
- `net-node/configs/mainnet.toml`: add `committee_selection`, vote byte
  configs, `quorum_stake_fraction` defaults
- `net-cluster/configs/sample-cluster.toml`: Leios committee selection examples

**Tests**:
- `quorum_after_enough_votes`: 4 voters, quorum=0.75, fires after 3rd
- `no_quorum_below_threshold`: 2/4 → no event
- `duplicate_voter_not_counted`: same voter twice → count=1
- `quorum_time_recorded`: `time_to_quorum_ms > 0`
- `leios_stats_counts`: verify counters increment

**Observable after**: Full cluster run produces: `EBGenerated` → N ×
`VoteProduced` → `QuorumReached { time_to_quorum_ms }`. Periodic
`LeiosStats` shows total vote bytes per node. Compare:
`--set committee_selection='"EveryoneVotes"'` vs
`'{"WfaLs":{"persistent_stake_fraction":0.3}}'` vs
`'{"StakeCentile":{"top_centile_of_stake":0.95}}'`

## Where we stand

### Already working
- **Protocols**: `LeiosNotify` (ID 18), `LeiosFetch` (ID 19) with full state
  machines, CBOR codecs, client+server, 124 tests.
- **Storage**: `net-core::store::LeiosStore` — content-addressed
  `(slot,hash) → blob` for EBs, TX bundles, votes.
- **Network dedup/routing**: `LeiosTracker` in the coordinator handles
  slot-windowed seen sets, per-offer peer tracking, RTT-based best-peer
  selection, pending-fetch dedup.
- **Per-peer tasks**: `spawn_leios_notify` request-next loop,
  `spawn_leios_fetch` command-driven.
- **Mux scheduling**: two-class PriorityWfq — Praos priority, Leios default.
- **Header/body parsing**: `HeaderInfo::{announced_eb,certified_eb}` (CIP-0164)
  and `LeiosBlockInfo` already parse the relevant fields off the wire.
- **Production stubs**: `BlockProducer::try_produce_eb` /
  `try_produce_votes` / `is_stage_boundary` emit opaque CBOR blobs at stage
  boundaries; `main.rs` injects them via `InjectLeiosBlock` /
  `InjectLeiosVotes`.
- **Config**: `leios_enabled`, `leios_dedup_window`, `stage_length_slots`,
  `eb_generation_probability`, `vote_generation_probability` wired. EB/vote
  validation delays exist in `ValidationConfig` but are **not** threaded
  into `DynamicConfig` yet.
- **Consensus routing**: `LeiosConsensus::handle_event` fetches offered
  EBs/TXs/votes, clears its in-flight map on receipt, logs receipts.

### What's missing
Everything that makes Leios mean something at the consensus layer:

| Gap | Note |
|---|---|
| EB/vote fake validation delay | config fields exist, not wired |
| EB candidate tracking per stage/election | no state |
| Out-of-order EB/vote buffering | no state |
| Vote aggregation, quorum detection | no state |
| Certificate formation | no type, no logic |
| Certified-EB extraction for RB header | producer doesn't read from consensus |
| Cert-backed chain-selection tie-breaking | deferred; requires real certs |
| Telemetry for stages/certs | new events needed |

## Guiding principles

1. **Leios is a layer on top of Praos, not a replacement.** Praos remains
   authoritative for chain selection until the MVP certs are trustworthy.
   `PraosConsensus` should not import from `LeiosConsensus` — the facade
   owns the cross-cutting calls (e.g. "what certified EB should the next RB
   advertise?").
2. **MVP is fake but end-to-end.** Votes stay opaque blobs; "signatures"
   are fake; quorum is a stake count against `total_stake`. The payoff is
   seeing certificates form and certified EBs land in RB headers in a
   running cluster. Real BLS comes later.
3. **TDD per commit.** Each step below is its own commit with its own
   failing-test-first. Keep diffs narrow so the review never needs to
   cross-reference.
4. **No speculative abstractions.** If a type exists once, don't factor
   it. If a method is called from one place, inline it. The shape will
   tell us when to generalize.

## Proposed commit sequence

### 1. Wire EB/vote validation delays

**Why**: Before we touch consensus state, make sure incoming Leios data
passes through the existing fake-delay validation pipeline the same way
RBs do. This gives Leios events a consistent "has been validated" gate
and keeps the consensus layer free of timing logic.

**Work**:
- Add `eb_validation_ms` / `vote_validation_ms` to `DynamicConfig` (next
  to the existing `rb_*` fields).
- Add `Validator::validate_eb(point, delay)` and
  `Validator::validate_votes(ids, delay)` — pure sleep-then-succeed,
  matching the existing RB pattern.
- Route `LeiosBlockReceived` / `LeiosVotesReceived` through the validator
  before consensus sees them. The outcome channel gains `EbValidated` /
  `VotesValidated` variants.
- `Consensus::handle_validation_outcome` forwards those to
  `self.leios.on_validated_*`.

**Tests**: validator returns the new outcome after the configured delay;
`LeiosConsensus::on_validated_eb` is called with the right point.

### 2. EB candidate tracking per stage

**Why**: Bare minimum of real Leios state. Once EBs flow through
validation, start sorting them into per-stage election buckets and
handle out-of-order arrivals.

**Work** in `leios.rs`:

```rust
struct ElectionState {
    stage: u64,
    candidates: Vec<EbCandidate>,        // ranked; freshest-first
    status: ElectionStatus,              // Open | Voting | Certified(EbKey) | Expired
}

struct EbCandidate {
    point: Point,
    producer: VoterId,                   // stub: slot-derived
    arrived_at: Instant,                 // for freshest-first tie-break
}

pub struct LeiosConsensus {
    // existing fields …
    stage_length_slots: u64,
    current_stage: u64,
    elections: HashMap<u64, ElectionState>,
    pending_ebs: Vec<(Point, Vec<u8>)>,  // stage hasn't opened yet
    dedup_window: u64,
}
```

- `on_slot(slot)` — advance `current_stage`, open/expire elections, prune
  outside the dedup window.
- `on_validated_eb(point, blob)` — place into the matching election;
  queue in `pending_ebs` if the stage hasn't opened; drain `pending_votes`
  (see next commit) that were waiting on this EB.
- `candidate_count(stage) -> usize` for telemetry/tests.

**Tests**: out-of-order EB arrives before its stage opens, then surfaces
when `on_slot` advances the stage; duplicate EBs are deduped; elections
outside the window are pruned.

### 3. Vote aggregation and certificate formation

**Why**: The first Leios behaviour that does something observable — we
start forming certificates.

**Work**:

```rust
struct ElectionState {
    // existing …
    votes: HashMap<EbKey, HashMap<VoterId, Vote>>,   // per-EB tallies
    quorum_threshold: u64,                            // stake-weighted
}

struct Certificate {
    stage: u64,
    eb: Point,
    voters: Vec<VoterId>,
    total_stake: u64,
    formed_at: Instant,
}

pub struct LeiosConsensus {
    // …
    certified_ebs: HashMap<u64, (Point, Certificate)>,  // stage -> winner
    pending_votes: Vec<(u64, VoterId, Vec<u8>)>,        // EB not yet seen
}
```

- `on_validated_votes(votes)` — attribute each vote to its EB; update
  tallies; when a candidate crosses `quorum_threshold`, form a
  `Certificate`, set `status = Certified(...)`, stash in `certified_ebs`.
- Votes for an unknown EB stash in `pending_votes`; drained when the EB
  arrives in commit 2's handler.
- Quorum threshold is stake-weighted from the existing `production.stake`
  / `production.total_stake` config. Default to 75% for MVP; make it
  configurable as `leios_quorum_percent`.
- Emit a `LeiosCertFormed` telemetry event with stage, point, voter count.

**Tests**: votes accumulate, cross quorum, form cert; votes arriving
before their EB buffer and later drain into a cert; votes beyond quorum
don't re-form the cert.

### 4. Produced RBs advertise certified EBs

**Why**: First user-visible end-to-end Leios behaviour in a cluster run.

**Work**:
- `LeiosConsensus::latest_certified_eb_for_parent(parent_slot) -> Option<(Point,CertMeta)>`
  returns the most recent certified EB applicable to a new RB built on
  top of `parent_slot` (typically the cert from the most recently
  completed stage before that slot).
- `Consensus::latest_certified_eb_for_parent` facade method.
- In `main.rs:148` (the stage-boundary production block), before
  `try_produce_block`, consult the facade and pass the resulting
  `(point, size)` / `certified_eb` flag through to
  `BlockProducer::try_produce_block`. The producer populates
  `HeaderInfo::announced_eb` / `HeaderInfo::certified_eb` in the
  produced header (the parser already supports both).
- New telemetry: `RbAdvertisedEb { stage, eb_point, rb_point }`.

**Tests**: producer with a cached certified EB emits a header whose
`HeaderInfo::certified_eb` is `Some(true)` and whose `announced_eb`
matches; cluster smoke run where two nodes produce, exchange, certify,
and re-advertise certified EBs within the dedup window.

**End of MVP.** At this point a cluster run can show real Leios activity
in cluster-events.jsonl: EBs produced, votes exchanged, certs formed,
subsequent RBs carrying certified EBs.

### 5. (Deferred) Cert-backed chain-selection tie-breaking

**Why**: This is the first step where Leios actually influences Praos
fork choice. Don't turn it on until certs come from real signatures,
otherwise a malicious producer can win fork races with fabricated
certificates.

**Shape**: in `PraosConsensus::select_chain`, when two candidate tips
tie on `block_no`, prefer the one whose header carries a valid
`certified_eb` matching one of `LeiosConsensus`'s stored certs. Gated
behind a `leios_cert_tiebreak_enabled` config flag, default false.

This is the natural place for the facade to become bidirectional, so
defer the design until commit 4 has run in a cluster long enough to
know what we actually need.

### Out of scope for this roadmap
- Real BLS signatures / signature verification (needs crypto decisions
  and likely a separate crate)
- Freshest-first transport-level scheduling inside LeiosFetch (CIP-0164
  suggests this; we may never need it for MVP)
- OCIN election-window enforcement at the network layer
- Merged block format (N2C only)
- Separate "certified EB range" protocol at Praos priority

## Open questions / decisions to make

1. **Quorum threshold default**: 75% of stake is the usual Leios
   research number, but for a small test cluster we probably want a
   knob. Decide in commit 3 whether to default to 75% or to 51% for
   easier cluster tests, and whether to ship a sample config override.
2. **Stage length vs. slot duration**: the default `stage_length_slots=20`
   with `slot_duration_ms=1000` gives 20-second stages. For fast
   cluster tests we'll want 200ms slots, which makes stages 4s — fine.
   Just note that production probabilities need rescaling.
3. **Where does `VoterId` come from?**: today `production.rs` emits
   `(slot, Vec<u8>)` vote IDs. Commit 3 needs to decide whether to
   derive `VoterId` from the producer's stake key or keep it opaque.
   MVP lean: keep opaque, use the byte blob as the key, document that
   collisions mean vote dedup falls through.
4. **Certificate lifetime**: how long do we keep certified EBs around?
   Probably `security_param_k` stages back, but needs a decision once
   we see memory behaviour in a cluster.
5. **What to telemetry-log**: stages advance silently today. Commit 2
   should add `LeiosStageAdvanced`/`LeiosStageExpired` so cluster
   dashboards can show election activity without grepping.

## Test strategy

- **Unit per commit** (TDD): every commit above lists at least one
  failing test to write first.
- **Cluster smoke after commit 4**: run the existing
  `net-cluster/configs/sample-cluster.toml` with `leios_enabled=true`,
  watch for `LeiosCertFormed` and `RbAdvertisedEb` events, confirm
  cluster still makes forward progress on the Praos chain.
- **No integration test harness for Leios yet**: if commit 4 reveals
  flakes, that's the signal to build one. Don't build it speculatively.

## File map

Everything below lives in `net-node/src/`:

- `consensus/mod.rs` — facade, gains `latest_certified_eb_for_parent`
  and cert-backed selection delegation in commit 5.
- `consensus/praos.rs` — untouched until commit 5 (then gains the
  cert-aware branch in `select_chain`, behind the gate flag).
- `consensus/leios.rs` — grows in commits 1–4: validation outcome
  handlers, election state, vote aggregation, cert formation, query
  methods for the producer.
- `validation.rs` — commit 1: EB/vote fake delay validators, new
  outcome variants.
- `config.rs` — commit 1: thread EB/vote delays into `DynamicConfig`;
  commit 3: `leios_quorum_percent`; commit 5: `leios_cert_tiebreak_enabled`.
- `production.rs` — commit 4: accept certified-EB input and populate
  `HeaderInfo` fields.
- `main.rs` — commit 4: consult facade before producing an RB.
- `telemetry.rs` — commits 2/3/4: `LeiosStageAdvanced`,
  `LeiosStageExpired`, `LeiosCertFormed`, `RbAdvertisedEb`.
