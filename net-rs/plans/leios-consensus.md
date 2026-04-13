# Leios Consensus — Next Steps

This document captures the roadmap for building the Leios consensus layer on
top of the existing Praos implementation. The network plumbing (protocols,
store, tracker, coordinator, production stubs) is complete; what follows is
the actual EB/vote/certificate logic plus the wiring that lets Praos see
certified EBs.

Commit `3c7eca140` split `consensus.rs` into `consensus/{mod,praos,leios}.rs`
and moved the offer→fetch routing into `LeiosConsensus`. That module is now
the home for everything below.

## Reference model: CIP-0164 / Linear Leios

This implementation follows the **Linear Leios** variant of CIP-0164. Key
properties of this model (validated against the spec and sim-rs):

1. **Per-EB elections, not per-stage.** Each EB has its own independent
   pipeline. There is no `stage_length_slots` grouping. Multiple EBs can
   be in-flight with overlapping voting periods.

2. **EB production is coupled to RB production.** An RB producer optionally
   announces an EB in the RB header (`announced_eb` field). EBs do not
   exist independently of RBs. Empty EBs are not announced.

3. **Pipeline timing per EB.** Given an EB announced in an RB at slot S:
   - S to S + 3×Δhdr: equivocation detection window
   - S + 3×Δhdr to S + 3×Δhdr + L_vote: voting window
   - S + 3×Δhdr + L_vote to S + 3×Δhdr + L_vote + L_diff: diffusion period
   - After S + 3×Δhdr + L_vote + L_diff: certificate may be included in RB

4. **Parameters** (from sim-rs defaults with 1s slots):
   - Δhdr = 1 slot (header diffusion time; sim-rs: `leios_header_diffusion_time_ms: 1000`)
   - L_vote = 5 slots (voting window; sim-rs: `linear_vote_stage_length_slots: 5`)
   - L_diff = 5 slots (diffusion window; sim-rs: `linear_diffuse_stage_length_slots: 5`)
   - Total pipeline: 3 + 5 + 5 = 13 slots per EB

5. **Election ID** = slot of the RB that announced the EB.

6. **Vote casting rule.** A node votes for an EB when ALL of:
   - The announcing RB header arrived within Δhdr of creation
   - No equivocating RB header detected for that slot
   - EB fully validated before 3×Δhdr + L_vote slots elapsed
   - The EB is announced by the latest RB in the voter's current chain
   - Voter passes committee selection (persistent or non-persistent sortition)

7. **Certificate formation.** Only the next RB producer aggregates votes
   into a certificate (not every node locally). For MVP we simplify:
   every node tracks tallies, and the RB producer consults the tally when
   producing.

## Immediate goal: vote bandwidth measurement

Validate the bandwidth load of the Leios voting mechanism under different
committee selection rules (wFA+LS, EveryoneVotes, StakeCentile). Three
phases of work, each independently useful:

**Phase 1** — DONE. Vote plumbing + structure + committee selection types.
Vote IDs carried through fetch pipeline, fetched votes re-injected for
epidemic flooding, structured fake vote bodies (130-180B), CommitteeSelection
enum with VoteDecision (PersistentVote / NonPersistentVote / NoVote).
EB/vote validation delays wired through the validator actor.

### Phase 2: EB-triggered voting with per-EB pipeline

Votes become reactive to validated EBs. Each EB gets its own election
with CIP-0164 pipeline timing. Committee selection gates who votes.

### Phase 3: Vote aggregation, quorum detection, certificates in RBs

Track votes per EB, detect quorum within pipeline timing, form
certificates. RB producers include certificates for eligible EBs.

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
- **Config**: `leios_enabled`, `leios_dedup_window`,
  `eb_generation_probability`, `vote_generation_probability` wired.
- **Validation delays**: `eb_validation_ms` / `vote_validation_ms` in
  `DynamicConfig`, routed through the validator actor. `EbValidated` /
  `VotesValidated` outcomes forwarded to `LeiosConsensus`.
- **Consensus routing**: `LeiosConsensus::handle_event` fetches offered
  EBs/TXs/votes, clears its in-flight map on receipt, submits to validator.
  `on_validated_eb` / `on_validated_votes` stub handlers log.
- **Slot ticks**: `consensus.on_slot(slot)` called from main loop (stub).

### What's missing
Everything that makes Leios mean something at the consensus layer:

| Gap | Note |
|---|---|
| Per-EB election tracking with pipeline timing | no state |
| EB-triggered vote production | votes still produced at stage boundaries |
| Vote aggregation, quorum detection | no state |
| Certificate formation | no type, no logic |
| Certified-EB extraction for RB header | producer doesn't read from consensus |
| Cert-backed chain-selection tie-breaking | deferred; requires real certs |
| Telemetry for elections/certs | new events needed |

## Guiding principles

1. **Follow CIP-0164 / Linear Leios.** Per-EB elections with pipeline
   timing (3×Δhdr + L_vote + L_diff), not stage-based grouping. Use
   sim-rs Linear Leios as the reference implementation.
2. **Leios is a layer on top of Praos, not a replacement.** Praos remains
   authoritative for chain selection until the MVP certs are trustworthy.
3. **MVP is fake but structurally correct.** Votes are opaque blobs;
   signatures are fake; quorum is a vote count. But the pipeline timing,
   per-EB election model, and certificate flow match the spec.
4. **TDD per commit.** Each step below is its own commit with failing tests
   first.
5. **No speculative abstractions.**

## Proposed commit sequence

### 1. Wire EB/vote validation delays — DONE

Commit `de6f1ff31`. Added `ValidateEb`/`ValidateVotes` command and
outcome variants, `#[derive(Clone)]` on `Validator`, `dyn_config` in
the actor, `eb_validation_ms`/`vote_validation_ms` in `DynamicConfig`.
`LeiosBlockReceived`/`LeiosVotesReceived` routed through validator.

### 2. Per-EB election tracking with pipeline timing

**Why**: The core Leios state model. Each validated EB gets its own
election object with pipeline phase tracking based on CIP-0164 timing.
Slot ticks advance elections through phases and prune old ones.

**Config** — new fields in `LeiosConfig` (or `ProductionConfig`):
- `leios_delta_hdr_slots: u64` (default 1) — header diffusion time in slots
- `leios_vote_window_slots: u64` (default 5) — L_vote
- `leios_diffuse_window_slots: u64` (default 5) — L_diff

**Types** in `leios.rs`:

```rust
/// Pipeline phase for an EB election (CIP-0164 Linear Leios).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PipelinePhase {
    /// Waiting for equivocation detection (3 × Δhdr slots).
    EquivocationCheck,
    /// Voting window open (L_vote slots).
    Voting,
    /// Votes diffusing (L_diff slots).
    Diffusing,
    /// Certificate may be included in an RB.
    CertEligible,
    /// Election expired / pruned.
    Expired,
}

/// Per-EB election state.
struct EbElection {
    eb_point: Point,
    eb_hash: [u8; 32],
    /// Slot the EB was announced (from Point::Specific).
    announced_slot: u64,
    phase: PipelinePhase,
    validated_at: Instant,
}
```

**Fields** on `LeiosConsensus`:
- `delta_hdr: u64, vote_window: u64, diffuse_window: u64` — pipeline params
- `current_slot: u64`
- `elections: HashMap<[u8; 32], EbElection>` — keyed by EB hash
- `pending_ebs: Vec<Point>` — EBs received before being validated (already handled by validator, may not be needed)

**Methods**:
- `on_slot(slot)` — advance `current_slot`, update phase of each election
  based on elapsed slots, prune expired elections
- `on_validated_eb(point)` — create `EbElection` in `EquivocationCheck`
  phase, compute `announced_slot` from point
- `phase_for_slot(announced_slot, current_slot) -> PipelinePhase` — pure
  function computing phase from timing params
- `elections_in_phase(phase) -> impl Iterator` — for tests/queries

**Phase transitions** (in `phase_for_slot`):
```
elapsed = current_slot - announced_slot
if elapsed < 3 * delta_hdr          → EquivocationCheck
if elapsed < 3 * delta_hdr + vote   → Voting
if elapsed < 3 * delta_hdr + vote + diff → Diffusing
else                                 → CertEligible
```

Prune elections where `elapsed > 3 * delta_hdr + vote + diff + dedup_window`.

**Tests**:
- `eb_creates_election`: validated EB → election exists in EquivocationCheck
- `election_advances_through_phases`: on_slot at each boundary → correct phase
- `phase_for_slot_pure_function`: unit test of the timing formula
- `duplicate_eb_deduped`: same EB hash twice → one election
- `old_election_pruned`: advance far enough → election removed
- `multiple_ebs_concurrent`: two EBs at different slots → independent elections

### 3. EB-triggered voting with committee selection

**Why**: Votes become reactive to EBs entering the Voting phase, gated
by committee selection. Replaces the stage-boundary vote production.

**Work** in `leios.rs`:
- On `on_slot`, for each election that just entered `Voting` phase:
  call `try_vote_on_eb(eb_hash, election_id)`
- `try_vote_on_eb`: committee selection → VoteDecision → build vote body
  → `InjectLeiosVotes` command
- `voted_ebs: HashSet<[u8; 32]>` — prevent double-voting

**Work** in `main.rs`:
- Remove `try_produce_votes()` block at stage boundaries
- Vote production now happens inside consensus on phase transitions

**Work** in `consensus/mod.rs`:
- Pass `CommitteeSelection`, stake, `dyn_config` to `LeiosConsensus`

**Tests**: same as original Phase 2 tests but triggered by phase
transition, not by `LeiosBlockReceived` directly.

### 4. Vote aggregation and certificate formation

**Why**: The first Leios behaviour that does something observable.

**Work**:

```rust
struct EbElection {
    // existing …
    votes: HashMap<Vec<u8>, ()>,    // voter_id → () (dedup)
    quorum_reached: bool,
}
```

- `on_validated_votes(vote_ids, vote_data)` — parse each vote to extract
  `endorser_block_hash` and `voter_id`, attribute to election, check quorum
- Votes for unknown EBs: buffer in `pending_votes`, drain when EB arrives
- Quorum: configurable fraction (default 75%), estimated from vote count
  × (total_stake / num_nodes)
- Emit `LeiosCertFormed` telemetry event

**Tests**: votes accumulate → quorum → cert; buffered votes drain; no
double-count.

### 5. Produced RBs advertise certified EBs

**Why**: First user-visible end-to-end Leios behaviour in a cluster run.

**Work**:
- `LeiosConsensus::certified_eb_for_rb(slot) -> Option<(Point, CertMeta)>`
  — returns the most recent cert-eligible EB whose full pipeline
  (3×Δhdr + L_vote + L_diff) has elapsed before `slot`
- `Consensus` facade method
- In `main.rs`, before `try_produce_block`, consult the facade and
  populate `HeaderInfo::announced_eb` / `HeaderInfo::certified_eb`
- Telemetry: `RbAdvertisedEb { eb_point, rb_point }`

**End of MVP.** Cluster run shows: EB announced in RB → votes exchanged
→ cert formed → subsequent RB carries certified EB.

### 6. (Deferred) Cert-backed chain-selection tie-breaking

Gated behind `leios_cert_tiebreak_enabled` config flag, default false.
Requires real signatures.

### Out of scope for this roadmap
- Real BLS signatures / signature verification
- Freshest-first transport-level scheduling inside LeiosFetch
- OCIN election-window enforcement at the network layer
- Merged block format (N2C only)
- Separate "certified EB range" protocol at Praos priority
- Equivocation detection (sim-rs notes: "We are not yet simulating equivocation")

## Open questions

1. **Quorum estimation**: with fake votes, how do we estimate stake from
   vote count? sim-rs uses VRF lottery results. We may need
   `num_expected_nodes` config to estimate `vote_count / num_nodes × total_stake`.
2. **EB production coupling**: currently EBs are produced at stage
   boundaries. For spec compliance they should be produced alongside RBs.
   Commit 3 or a pre-commit should move EB production into `try_produce_block`.
3. **Δhdr in slots vs ms**: sim-rs uses `leios_header_diffusion_time_ms`
   (wall clock) but our pipeline checks are slot-based. With 1s slots and
   1000ms Δhdr these are equivalent. Document the assumption.
4. **Certificate lifetime / pruning**: how long to keep elections after
   CertEligible? Probably `security_param_k` slots.

## Test strategy

- **Unit per commit** (TDD): every commit above lists tests to write first.
- **Cluster smoke after commit 5**: run sample-cluster.toml with
  `leios_enabled=true`, watch for cert events, confirm Praos progress.
- **No integration test harness for Leios yet**: build one if commit 5
  reveals flakes.

## File map

Everything below lives in `net-node/src/`:

- `consensus/mod.rs` — facade; gains `on_slot`, `certified_eb_for_rb`
- `consensus/praos/` — untouched until commit 6
- `consensus/leios.rs` — grows in commits 2–5: per-EB elections, pipeline
  timing, vote aggregation, cert formation, queries for the producer
- `validation.rs` — commit 1 (done): EB/vote fake delay validators
- `config.rs` — commit 2: pipeline timing params; commit 4: quorum config
- `production.rs` — commit 5: accept certified-EB input, populate HeaderInfo
- `main.rs` — commit 3: remove stage-boundary votes; commit 5: consult facade
- `telemetry.rs` — commits 4/5: `LeiosCertFormed`, `RbAdvertisedEb`
