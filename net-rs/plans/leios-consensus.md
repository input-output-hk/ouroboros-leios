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
149 tests across the workspace. Key Leios tests:
- Pipeline phase boundaries (pure function)
- Election lifecycle (create → advance through phases → prune)
- Voting (phase trigger, no double vote, no vote during equivocation check)
- Vote aggregation (accumulate, dedup, quorum threshold)
- Certified EB header roundtrip (11-field CBOR with `certified_eb=true`)

### Transaction & EB production (complete)
- **Shared mempool**: `Mempool` struct accumulates txs from local Poisson
  generator and peer receipt. `drain_up_to` for RB body, `drain_all` for
  EB overflow. Configurable capacity (`mempool_capacity`, default 10K).
- **Mempool-driven EB production**: `try_produce_block` checks mempool —
  if pending bytes ≤ `rb_body_max_bytes` (default 64KB), txs go in the RB
  body directly; otherwise ALL txs drain into a content-addressed EB manifest
  `[slot, [tx_hash, ...]]` and the RB body is empty with the EB announced
  in the header's `announced_eb` field (12-field header with hash+size).
  Old `is_stage_boundary` / `stage_length_slots` lottery removed.
- **Pull-model TxSubmission**: demand-driven dissemination — peer's server
  requests tx IDs via `TxsRequested`, application peeks mempool and responds
  with `ProvideTxs` routed to that specific peer. Replaces the push-based
  `SubmitTransaction` broadcast that flooded per-peer command channels.
- **Pre-mempool tx validation**: received transactions go through
  `spawn_tx_validator` with `tx_validation_ms` + per-byte scaling before
  entering the mempool, modeling Cardano Phase 1 validation.

### Cluster-verified
25-node cluster with `leios_enabled=true`, `rb_generation_probability=0.05`,
`tx_rate=2.0`: EBs produced → elections track pipeline phases → votes
produced and flooded → quorum detected → RB headers carry `certified_eb=true`.
Zero peer evictions, 100% EB propagation.

## What's next

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

### EB selection policy

When multiple EBs reach CertEligible, `has_certified_eb()` returns
`any(quorum && CertEligible)` with no preference. Need a selection
strategy (e.g. oldest-first to minimize latency, or per-slot to avoid
starvation).

### Deferred

- Cert-backed chain-selection tie-breaking (requires real signatures)
- Real BLS signatures / verification
- Equivocation detection
- Freshest-first transport scheduling (security-relevant: prevents withholding
  attacks where adversaries release stale EBs to waste pipeline slots)
