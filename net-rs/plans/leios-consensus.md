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
- **Committee selection**: WfaLs (wFA persistent + LS non-persistent),
  EveryoneVotes, StakeCentile. Persistent votes ~130B, non-persistent ~180B.
- **Stake registry**: every node holds the network-wide
  `Vec<StakeEntry { node_id, stake }>` at startup, mirroring what a real
  node reads from the ledger at epoch boundaries.

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
- **WFA+LS committee** (`consensus/leios/wfa.rs`):
  - **Persistent committee** (wFA): `allocate_persistent_seats(registry,
    persistent_voters, seed)` — `persistent_voters` independent draws from the
    cumulative stake distribution. Identical inputs (registry + seed) on every
    node → identical committee, no communication. `committee_seed` is
    `genesis_time_unix` so per-startup is per-epoch in this model.
  - **Non-persistent lottery** (LS): per-EB, each pool computes a deterministic
    eligibility signature `Blake2b(voter_id ‖ eb_hash ‖ eb_slot)` (modeling the
    CIP-0164 VRF output). The signature seeds an RNG that runs
    `non_persistent_voters` Bernoulli trials at `p = stake/total`; the win
    count is the pool's NPV weight. Both prover and aggregator compute the
    count from the signature and the registry-resolved stake — the count
    itself is **never on the wire**.
  - **build_committee** dispatches: WfaLs → seat allocation; EveryoneVotes →
    every nonzero-stake pool gets one seat; StakeCentile → top stakers
    (sorted descending, prefix to top centile) get one seat each.
- **EB-triggered voting**: `on_slot` detects elections entering Voting phase,
  calls `try_vote_on_eb`. A pool may emit up to two bodies per EB:
  one PV iff `persistent_seats ≥ 1`, and one NPV iff its lottery yielded ≥1
  win. EveryoneVotes / StakeCentile only emit PV.
- **Vote aggregation**: `on_validated_votes` derives each body's weight —
  PV = `committee[voter_id]`, NPV = `count_npv_wins(eligibility_signature,
  stake[voter_id], total_stake, n_npv)` — and sums weights for quorum.
  Threshold: `Σ weight ≥ quorum_weight_fraction × expected_committee_size`,
  where `expected_committee_size = persistent_voters + non_persistent_voters`
  (default 480 + 120 = 600, matching sim-rs e30087cdf).
- **Certified EB in RB headers**: `has_certified_eb()` checks for quorum +
  CertEligible phase. `try_produce_block` emits 11-field header with
  `certified_eb=true`.

### Module structure
```
consensus/
  mod.rs            — facade (on_slot, handle_event, on_validation_outcome, has_certified_eb)
  leios/
    mod.rs          — LeiosConsensus struct, event routing, slot tick, validation handlers,
                      cached persistent committee + stake registry
    pipeline.rs     — PipelinePhase, PipelineConfig, EbElection, phase_for_elapsed
    voting.rs       — VotingConfig, try_vote_on_eb (PV emission + NPV lottery)
    aggregation.rs  — record_vote (weight attribution, dedup, quorum detection)
    wfa.rs          — allocate_persistent_seats, build_committee,
                      npv_eligibility_signature, count_npv_wins
  praos/            — unchanged
```

### Test coverage
173 tests across the workspace. Key Leios tests:
- Pipeline phase boundaries (pure function)
- Election lifecycle (create → advance through phases → prune)
- Voting (PV-only, NPV-only, PV+NPV emission)
- wFA committee allocation (deterministic, total seats = N_pv,
  zero-stake → no seats, stake proportionality)
- NPV signature determinism + reproducibility of win count
- Vote aggregation (weight-summed, dedup, quorum threshold)
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

### Stake distribution

`net-cluster::topology::distribute_stake` strategies:
- `"equal"`: every node gets `total/n`.
- `"mainnet-shaped"`: `MAINNET_RELAY_FRACTION` (0.71, from analysis of
  `data/simulation/pseudo-mainnet/topology-v2.yaml`) of nodes get stake 0
  (relays); the remaining pools split the total uniformly. Captures the
  saturation-flat shape of Cardano mainnet's pool distribution.

### Cluster-verified
25-node cluster with `leios_enabled=true`, `rb_generation_probability=0.05`,
`tx_rate=2.0`, default WfaLs (480 PV + 120 NPV → committee size 600, quorum
threshold 450): per-node persistent_seats range 8..27 (mean 19.2, sum 480),
quorum reached on every EB at voted_weight ≥ 450, RbCertifiedEb fires for
every certified RB. Zero peer evictions, 100% EB propagation, no rollbacks.

## What's next

### Ledger state for EB transactions

Once EBs carry real transactions (mempool-driven production above), some form
of transaction validation and conflict detection is needed. Currently there is
no ledger state concept beyond fake validation delays. Work needed:
- Track spent transaction inputs to detect double-spends across EBs
- Validate EB transaction closures against ledger state from the prior RB
- Decide whether certified EB transactions skip re-validation (per CIP-0164)
  or get validated inline

### Telemetry

Telemetry now surfaces three Leios-specific events alongside RBGenerated/EBGenerated:
- `LeiosQuorumReached { node, eb_slot, voted_weight, voters }` — per-node, when
  this node's local weight tally first crosses
  `quorum_weight_fraction × expected_committee_size`.
  Multiple per EB (one per node that observes quorum) — useful for quorum-propagation
  latency analysis.
- `RbCertifiedEb { node, rb_slot, eb_slot }` — per-RB, fired only on the producing
  node when an RB header is emitted with `certified_eb=true`.
- `LeiosElectionExpired { node, eb_slot, had_quorum, voted_weight, voters }` — fired
  when an election is pruned past `dedup_window`, with final tally for analysis.

### EB selection policy

When multiple EBs reach CertEligible, `has_certified_eb()` returns
`any(quorum && CertEligible)` with no preference. Need a selection
strategy (e.g. oldest-first to minimize latency, or per-slot to avoid
starvation).

### TX bitmap selection policy

`FetchLeiosBlockTxs` carries a `BTreeMap<u16, u64>` bitmap for selective TX
addressing, plumbed end-to-end. Consensus always sends `BTreeMap::new()` (i.e.
fetch all txs). No policy yet for "fetch only txs not already in mempool" — the
intended saving the bitmap is meant to enable.

### Per-epoch refresh of the wFA committee

The persistent committee is currently allocated once at startup using
`genesis_time_unix` as the seed. A real node would re-derive it at each
epoch boundary. Once we model epochs, swap `committee_seed` for
`epoch_nonce` and recompute on rotation.

### Deferred

- Cert-backed chain-selection tie-breaking (requires real signatures)
- Real BLS signatures / verification (the eligibility signature is currently
  a deterministic Blake2b stand-in for the VRF output)
- Equivocation detection
- Freshest-first transport scheduling (security-relevant: prevents withholding
  attacks where adversaries release stale EBs to waste pipeline slots)
