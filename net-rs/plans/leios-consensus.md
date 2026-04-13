# Leios Consensus

## Reference model: CIP-0164 / Linear Leios

This implementation follows the **Linear Leios** variant of CIP-0164,
validated against the spec and sim-rs (`sim-core/src/sim/linear_leios.rs`).

- **Per-EB elections.** Each EB has its own independent pipeline. Multiple
  EBs can be in-flight with overlapping voting periods.
- **Pipeline timing per EB** (slot S = announcement):
  `EquivocationCheck [S, S+3Δhdr)` → `Voting [S+3Δhdr, S+3Δhdr+L_vote)`
  → `Diffusing [S+3Δhdr+L_vote, S+3Δhdr+L_vote+L_diff)` → `CertEligible`
- **Default parameters** (1s slots): Δhdr=1, L_vote=5, L_diff=5 → 13 slot pipeline.
- **Committee selection**: WfaLs (persistent + non-persistent), EveryoneVotes,
  StakeCentile. Persistent votes ~130B, non-persistent ~180B.

## What's implemented

### Network layer (complete)
- LeiosNotify (ID 18) + LeiosFetch (ID 19) protocols, CBOR codecs, client+server
- LeiosStore: content-addressed `(slot,hash) → blob` for EBs, votes
- LeiosTracker: slot-windowed dedup, per-offer peer tracking, RTT-based fetch routing
- Two-class PriorityWfq scheduling: Praos priority, Leios default
- CIP-0164 header parser: `HeaderInfo::announced_eb`, `HeaderInfo::certified_eb`
- Epidemic vote flooding (re-inject fetched votes to LeiosStore)

### Consensus layer (complete — MVP)
- **Validation delays**: `eb_validation_ms`/`vote_validation_ms` in DynamicConfig,
  routed through the validator actor. `EbValidated`/`VotesValidated` outcomes.
- **Per-EB elections**: `EbElection` with `PipelinePhase` tracking, `PipelineConfig`
  with `phase_for_elapsed()`. Elections created on `on_validated_eb`, advanced by
  `on_slot`, pruned after `dedup_window`.
- **EB-triggered voting**: `on_slot` detects elections entering Voting phase,
  calls `try_vote_on_eb` with `CommitteeSelection::decide_vote`. Produces
  structured `VoteBody` (130-180B CBOR) and injects via `InjectLeiosVotes`.
- **Vote aggregation**: `on_validated_votes` parses vote bodies, extracts
  `endorser_block_hash` + `voter_id`, attributes to elections. Quorum at ≥3
  unique voters (MVP threshold).
- **Certified EB in RB headers**: `has_certified_eb()` checks for quorum +
  CertEligible phase. `try_produce_block` emits 11-field header with
  `certified_eb=true`.

### Module structure
```
consensus/
  mod.rs            — facade (on_slot, handle_event, on_validation_outcome, has_certified_eb)
  leios/
    mod.rs          — LeiosConsensus struct, event routing, slot tick, validation handlers
    pipeline.rs     — PipelinePhase, PipelineConfig, EbElection, phase_for_elapsed
    voting.rs       — VotingConfig, try_vote_on_eb (committee selection + vote body building)
    aggregation.rs  — record_vote (vote attribution, dedup, quorum detection)
  praos/            — unchanged
```

### Test coverage
135 tests across the workspace. Key Leios tests:
- Pipeline phase boundaries (pure function)
- Election lifecycle (create → advance through phases → prune)
- Voting (phase trigger, no double vote, no vote during equivocation check)
- Vote aggregation (accumulate, dedup, quorum threshold)
- Certified EB header roundtrip (11-field CBOR with `certified_eb=true`)

### Cluster-verified
25-node cluster with `leios_enabled=true`: EBs produced → elections track
pipeline phases → votes produced and flooded → quorum detected → RB headers
carry `certified_eb=true` (429→430 byte header size increase).

## What's next

### Mempool-driven EB production

Currently EBs are produced probabilistically at stage boundaries
(`is_stage_boundary` + `eb_generation_probability` lottery). Per CIP-0164,
EBs should be produced **when the mempool has transactions that won't fit
in the RB**, not on a fixed schedule.

**Work needed**:
- EB production moves into `try_produce_block`: when producing an RB, if
  the mempool has excess transactions beyond what fits in the RB body,
  build an EB from the overflow and announce it in the RB header
  (`announced_eb` field)
- Remove `is_stage_boundary` / `stage_length_slots` from EB production path
- The fake tx generator may need tuning: current Poisson rate may be too
  low to overflow RBs. Need configurable tx rate high enough that EBs are
  actually needed
- RB body size limit config (currently RBs are tiny fake blocks with no tx
  payload)
- EB selection policy when multiple EBs reach CertEligible: `has_certified_eb()`
  currently returns `any(quorum && CertEligible)` with no preference. Need a
  selection strategy (e.g. oldest-first to minimize latency, or newest-first)

### Stake-weighted quorum

Current quorum is a flat ≥3 voters. Should be stake-weighted:
`Σ(voter_stake) ≥ quorum_fraction × total_stake`. Requires either:
- Encoding stake in vote bodies (MVP approach), or
- Looking up voter stake from a registry (closer to spec)

Config field `quorum_stake_fraction` already exists (default 0.75).

### Ledger state for EB transactions

Once EBs carry real transactions (mempool-driven production above), some form
of transaction validation and conflict detection is needed. Currently there is
no ledger state concept beyond fake validation delays. Work needed:
- Track spent transaction inputs to detect double-spends across EBs
- Validate EB transaction closures against ledger state from the prior RB
- Decide whether certified EB transactions skip re-validation (per CIP-0164)
  or get validated inline

### Telemetry

Missing events that would help cluster analysis:
- `LeiosCertFormed { node, eb_point, vote_count }`
- `RbCertifiedEb { node, rb_point, eb_point }`
- `LeiosElectionExpired { node, eb_point, had_quorum }`

### Deferred

- Cert-backed chain-selection tie-breaking (requires real signatures)
- Real BLS signatures / verification
- Equivocation detection
- Freshest-first transport scheduling (security-relevant: prevents withholding
  attacks where adversaries release stale EBs to waste pipeline slots)
- `announced_eb` hash+size in RB headers (currently only `certified_eb` bool)
