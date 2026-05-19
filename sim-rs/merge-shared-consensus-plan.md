# Plan: lift CIP-0164 features into shared-consensus, then collapse sim-rs's linear_leios onto it

## Context

`shared-consensus` was extracted from `net-rs` first (branch `prc/con-rs`) as a sans-IO
peer of both `net-rs/` and `sim-rs/`. The eventual goal is to retire
`sim-core/src/sim/linear_leios.rs` (≈2.3 kloc, including a ~600-line broken
mempool with unbounded backlogs) and have `sim-rs` drive `LeiosState` /
`PraosState` directly. This branch (`prc/con-rs`) is rebased on
`prc/sim-rs-voting`, so the wFA + LS voting unification (sim-rs's per-voter
VRF schedule → con-rs's persistent committee + NPV lottery) is already in
place.

This plan does **not** start by migrating `sim-rs`. It starts by upgrading
`shared-consensus` to host the CIP-0164 pieces that currently live in either `sim-rs`
or `net-rs`'s wrapper, then verifying `net-rs` still drives correctly. The
sim-rs collapse is a follow-on phase.

The user's framing: *"this is a major rewrite, and we can be bold."* No
piecewise functional milestones inside the con-rs upgrade — land the whole
new surface, then port consumers.

## Decisions baked in

- **Voting model:** wFA + LS persistent committee + NPV lottery (con-rs's
  current model). The sim's `vrf_probabilities` × per-voter trial schedule is
  retired with the merge of `prc/sim-rs-voting`.
- **EB body shape:** TX-by-references (`LinearWithTxReferences`). Inlined-TX
  EB code paths in sim-rs are not preserved.
- **Attack vectors** (`EBWithholdingSender`, `generate_withheld_txs`,
  `behaviours.withhold_*`): explicitly **out of scope**; will be re-added
  later as an attacker-wrapper layer outside con-rs.
- **Spent-input ledger** (`LedgerState { spent_inputs, seen_blocks }`):
  not preserved. Will be either an Acropolis feature or a fake micro-ledger
  on net-rs's side.
- **TX propagation** (TxSubmission mini-protocol): wire-format pieces stay
  in `net-core/src/protocols/txsubmission/`. The per-peer-advertised-set
  tracking moves into con-rs as part of the mempool (see Work Item 3).
  The active half (LeiosFetch / `FetchLeiosBlockTxs`) is already in
  `leios.rs`.

## Status read (verified)

- con-rs `LeiosEffect` has `FetchLeiosBlockTxs` / `match_eb_tx_response` /
  `RecordLeiosEbManifest` — the active-fetch half of TX propagation. ✓
- con-rs has **no** TxSubmission surface. The state lives in
  `net-rs/net-node/src/mempool.rs::Mempool` (queue + per-peer advertised
  set + `peek_unannounced_for_peer`). The wire half is in
  `net-core/src/protocols/txsubmission/mod.rs`. ✗ in con-rs.
- Multi-peer fetch routing is hard-coded in net-rs's coordinator
  (`net-core/src/multi_peer/coordinator.rs:593-738`,
  `LeiosTracker::pick_*_fetch_peer*`). con-rs `PraosEffect::FetchBlockRange`
  carries only `peer_id: Option<PeerId>` hint; `LeiosEffect` carries no
  peer at all. ✗ in con-rs (deliberately so far).

## Work items (in con-rs)

### 1. Should-vote-for predicates

CIP-0164 voting validity checks currently in sim-rs's `should_vote_for`
(`linear_leios.rs:1629-1662`):

- `LateEB` — EB received after `eb_slot + 3·Δhdr + L_vote`.
- `LateRBHeader` — chain-tip RB header arrived after `eb_slot + Δhdr`.
- `WrongEB` — chain-tip RB doesn't reference this EB.
- `MissingTX` — at least one referenced TX is unknown locally
  (relevant in `LinearWithTxReferences` mode, which is the only one
  preserved).

These are real CIP-0164 voting predicates and belong in con-rs. Land them
inside `LeiosState::decide_vote` (currently in `shared-rs/consensus/src/leios.rs:256`).
Inputs the predicate needs:

- EB-arrival timestamp (already implicitly tracked via `on_eb_offered` /
  `on_eb_received` paths — extend `Elections::announce` to carry it).
- Latest adopted RB-header arrival time and the EB id it references —
  injected via a new `LeiosState` setter or via the `decide_vote`
  callsite reaching into `PraosState` (preferred: pass in as args, keep
  the two state machines decoupled).
- A `has_tx(tx_id)` query — implement against the new shared mempool
  (Work Item 3).

Add a `NoVoteReason` enum to `LeiosEffect` (mirroring sim-rs's
`model::NoVoteReason` minus the IB-era variants) so the wrapper can emit
`track_no_vote` telemetry. Carry as a sibling effect:
`LeiosEffect::NoVote { eb_hash, eb_slot, reason: NoVoteReason }` — parallel
to `EmitVote`, simpler to match in adapters, mirrors sim-rs's existing
`track_no_vote` telemetry shape.

**Files touched:**
- `shared-rs/consensus/src/leios.rs` (decide_vote, LeiosEffect, on_slot's
  EligibleToVote handling)
- `shared-rs/consensus/src/elections.rs` (extend `EbElection` with `seen_at`,
  thread through `announce`)

### 2. Pluggable multi-peer fetch strategy

Currently the `peer_id` in `PraosEffect::FetchBlockRange` is just a hint;
the policy lives in net-rs's coordinator
(`pick_block_fetch_peer` / `LeiosTracker::pick_block_fetch_peer` etc.,
RTT-min over a fragment-scan). Sim-rs has a different policy
(`RelayStrategy::{RequestFromAll, RequestFromFirst}` plus per-message
dedup).

Lift the abstraction into con-rs as **four separate traits** — one per
traffic class — so each can be swapped independently as algorithms
evolve:

```rust
// shared-rs/consensus/src/fetch.rs (new)
pub trait BlockFetchPolicy {
    fn pick(&self, point: &Point, candidates: &[PeerId]) -> Vec<PeerId>;
}
pub trait EbFetchPolicy {
    fn pick(&self, point: &Point, candidates: &[PeerId]) -> Vec<PeerId>;
}
pub trait EbTxsFetchPolicy {
    fn pick(&self, point: &Point, bitmap: &BTreeMap<u16, u64>,
            candidates: &[PeerId]) -> Vec<PeerId>;
}
pub trait VoteFetchPolicy {
    fn pick(&self, votes: &[(u64, Vec<u8>)],
            candidates: &[PeerId]) -> Vec<PeerId>;
}
```

`FetchBlockRange` and the Leios fetch effects gain a `peers: Vec<PeerId>`
field (the *plural* matters for `RequestFromAll`-style policies — that's
how sim-rs amortizes loss). con-rs supplies two stock implementations,
each implementing **all four** traits to make wiring trivial in the
default case:

- `LowestRttFirst` — wraps an injected RTT oracle, mirrors net-rs today.
- `BroadcastN` — fan out to N peers; degenerates to `RequestFromAll` for
  N=∞ and `RequestFromFirst` for N=1.

Net-rs and sim-rs each pick a stock impl for all four (or substitute a
custom impl for a single class — e.g., broadcast votes while keeping
RTT-min for blocks).

The candidate-peer set itself (`offered_by[point] = Set<PeerId>` + RTT
cache) — currently `net-core/src/multi_peer/leios_tracker.rs` — moves
into `shared-rs/consensus/src/fetch.rs` next to `FetchPolicy`. Pure bookkeeping; both
consumers need the same shape; net-core's tracker collapses to a thin
re-export or is deleted.

**Files touched:**
- `shared-rs/consensus/src/fetch.rs` (new; four `*FetchPolicy` traits + stock impls +
  candidate-set tracker)
- `shared-rs/consensus/src/lib.rs` (re-export)
- `shared-rs/consensus/src/praos.rs` (FetchBlockRange effect; `PraosState::new` takes
  `Box<dyn BlockFetchPolicy>`; in_flight policy adapts)
- `shared-rs/consensus/src/leios.rs` (FetchLeiosBlock / FetchLeiosBlockTxs /
  FetchLeiosVotes effects; `LeiosState::new` takes
  `Box<dyn EbFetchPolicy>`, `Box<dyn EbTxsFetchPolicy>`,
  `Box<dyn VoteFetchPolicy>`)
- net-rs's coordinator drops its `pick_*` calls; uses the policies con-rs
  hands back the candidate list for.
- `net-core/src/multi_peer/leios_tracker.rs` collapses into a thin
  re-export of `con_rs::fetch::CandidateTracker` (or deleted).

### 3. Common mempool — sans-IO state machine, validation via effects

Pull `net-node/src/mempool.rs::Mempool` into `shared-rs/consensus/src/mempool.rs` as
a third sans-IO state machine alongside `PraosState` and `LeiosState`.
Sim-rs's mempool is **not** the source of truth — its design (unbounded
local + peer backlog `VecDeque`s, conflict-by-`input_id`,
`linear-tx-max-age-slots` aging) is the broken model that motivated
this work. Net-rs's design (bounded queue, per-peer advertised set, no
backlog) is the keeper.

Validation uses the **existing effect / on_xx pattern** — the same
shape as `LeiosEffect::ValidateEb` + `on_validated_eb`,
`LeiosEffect::ValidateVotes` + `on_validated_votes`,
`PraosEffect::ValidatorApply` + `on_block_applied` /
`on_block_apply_failed`. No `MempoolValidator` trait. This keeps the
boundary uniformly event-based, and ports cleanly to Acropolis later
(swap the I/O wrapper, not the trait surface).

Effect type:

```rust
pub enum MempoolEffect {
    /// Submit a TX body to the validator (consumer's I/O wrapper picks
    /// the actual validator — net-rs's ledger, sim-rs's mock, future
    /// Acropolis service).
    ValidateTx { tx_id: TxId, body: Vec<u8> },
    /// Advertise newly-mempooled TXs to a peer's TxSubmission server.
    AdvertiseTx { peer_id: PeerId, tx_ids: Vec<TxId> },
    /// Telemetry: a TX was dropped (overflow, conflict, etc.).
    TxRejected { tx_id: TxId, reason: TxRejectReason },
}
```

Public API (mirroring the on_xx style of the other state machines):

- `on_tx_offered(peer_id, tx_id)` → `Vec<MempoolEffect>` (decides whether
  to request the body and from whom).
- `on_tx_received(peer_id, tx_id, body)` → emits `ValidateTx`.
- `on_tx_validated(tx_id, body, body_size)` → admits to the queue; may
  emit `AdvertiseTx` to peers that haven't seen it; may emit
  `TxRejected` if the bounded queue overflows.
- `on_tx_validation_failed(tx_id, reason)` → emits `TxRejected` and
  cleans up.
- `on_block_applied(included_tx_ids)` / `on_block_rolled_back(target)`
  invalidate included TXs (sim-rs's `remove_rb_txs_from_mempool` /
  `remove_eb_txs_from_mempool` collapse to id-list inputs here — the
  EB-or-RB body doesn't cross con-rs).
- Pure queries: `peek_up_to(max_size)`, `peek_unannounced_for_peer`,
  `current_tx_ids`, `get_body_by_id`.

Bounded-size policy (`max_size_bytes`) lives inside the state machine;
rejection on overflow emits `TxRejected`, never "go to backlog."

Net-rs's I/O wrapper handles `ValidateTx` by calling its real ledger,
then feeds the result back via `on_tx_validated` /
`on_tx_validation_failed`. Sim-rs's wrapper does the same against its
mock validator (currently `TransactionConfig::Mock` / `Real`). The
unbounded backlog is gone.

**Files touched:**
- `shared-rs/consensus/src/mempool.rs` (new; lifted from `net-rs/net-node/src/mempool.rs`)
- `shared-rs/consensus/src/lib.rs` (re-export `MempoolState`, `MempoolEffect`,
  `TxRejectReason`)
- `net-rs/net-node/src/consensus/leios/mod.rs` updated to drive the
  con-rs `MempoolState` via its effect/on_xx surface.
- Delete `net-node/src/mempool.rs`.

### 4. Wire the `LeiosState` into net-node's adapter

After Work Items 1–3, walk through `net-node/src/consensus/leios/mod.rs`
and `consensus/praos/mod.rs` to make sure:

- `decide_vote` callers feed in the now-required RB-header-seen and
  chain-tip-EB inputs from `PraosState` (a small accessor on
  `PraosState`: `latest_adopted_rb_header_arrival() -> Option<Instant>`,
  `latest_adopted_eb_announcement() -> Option<[u8;32]>`).
- The `MempoolValidator` impl on net-rs's side stays
  byte-identical-functional with what mempool.rs does today.
- `FetchPolicy` implementation on net-rs side reproduces today's
  RTT-min behavior.

This is the "make sure net-rs still works" pass. The branch must pass
`cargo test` in `con-rs/`, `net-rs/`, and a focused smoke test on
net-rs's node before we even *open* the sim-rs collapse.

## Critical files

- `shared-rs/consensus/src/leios.rs` — adds NoVote, RBHeader/EB-context inputs to
  `decide_vote`, expands `LeiosEffect`.
- `shared-rs/consensus/src/elections.rs` — `EbElection.seen_at`; `announce` API.
- `shared-rs/consensus/src/praos.rs` — `FetchBlockRange::peers: Vec<PeerId>`;
  accessors for adapters.
- `shared-rs/consensus/src/fetch.rs` — **new**; four `*FetchPolicy` traits + stock
  impls + candidate-set tracker (lifted from net-rs `LeiosTracker`).
- `shared-rs/consensus/src/mempool.rs` — **new**; lifted from
  `net-rs/net-node/src/mempool.rs` as a sans-IO `MempoolState` with
  `MempoolEffect::{ValidateTx, AdvertiseTx, TxRejected}` surface.
- `shared-rs/consensus/src/lib.rs` — new re-exports.
- `net-rs/net-node/src/consensus/leios/mod.rs` — adapter updates.
- `net-rs/net-node/src/consensus/praos/mod.rs` — adapter updates.
- `net-rs/net-node/src/mempool.rs` — **deleted**, replaced by re-export.
- `net-rs/net-core/src/multi_peer/coordinator.rs` — drops in-house
  `pick_*` selectors, defers to `FetchPolicy`.

## Out of scope

Not part of this plan, will be follow-up branches:

- Replacing `sim-core/src/sim/linear_leios.rs` with a con-rs adapter.
  (After this work lands and net-rs is verified.)
- Re-introducing attack-vector hooks (`EBWithholdingSender`,
  `late_tx_attack`, `behaviours.withhold_*`) on top of con-rs as a
  separate adversary-wrapper layer.
- Acropolis / micro-ledger spent-input tracking.

## Verification

- `cd /home/prc/leios-net-rs/con-rs && cargo test` — every state machine
  has its own `#[cfg(test)] mod tests`. New tests required for:
  - `decide_vote` with each `NoVoteReason` predicate firing.
  - `BroadcastN` (as `BlockFetchPolicy` and `EbFetchPolicy`) on N=1,
    N=2, N=∞.
  - `MempoolState` round-trip: `on_tx_offered` →
    `MempoolEffect::ValidateTx` → `on_tx_validated` → admit, including
    overflow path that emits `TxRejected` (no backlog).
- `cd /home/prc/leios-net-rs/con-rs && cargo clippy --all-targets -- -D warnings`.
- `cd /home/prc/leios-net-rs/net-rs && cargo test` — confirm no
  regressions.
- `cd /home/prc/leios-net-rs/net-rs && cargo run -p net-node ...` —
  smoke a small two-node session and watch logs for `quorum reached`,
  `fork switch`, `block validated`. Compare against pre-merge baseline
  on the same network config.
- Sim-rs is **not** exercised in this branch's CI — sim-rs is still
  consuming the old `linear_leios.rs` and that path remains intact
  until the follow-on branch.
