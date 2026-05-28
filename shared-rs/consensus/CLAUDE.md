# shared-consensus

Sans-IO Cardano consensus core. Hosts the protocol pieces that every
Cardano-Leios implementation must agree on: longest-chain selection
(Praos), Linear Leios EB elections + voting (CIP-0164), committee
selection (wFA + LS), pipeline phase math, vote aggregation.

This crate is a **peer of `net-rs/` and `sim-rs/`**, not a child of
either. Both consume it via
`path = "../../shared-rs/consensus"`. It lives under the `shared-rs/`
workspace so additional shared crates (e.g. `tcp-model`) can sit
alongside it without a circular dependency on either consumer.

## Discipline

These rules are why this crate exists. Breaking them defeats the point
of the extraction. The behaviour subsystem has its own narrower
rule-set in [`src/behaviour/README.md`](src/behaviour/README.md);
everything below applies to it as well.

### 1. Sans-IO

No `tokio`, no networking, no clock reads, no file I/O.

- Time is **injected** as `Instant` parameters on methods that need it
  (`on_block_received`, `retry_select_chain`, …). The state machine
  never calls `Instant::now()` or `SystemTime::now()` itself.
- Randomness is **deterministic and stake-keyed** — all uses go through
  `committee.rs` helpers seeded by `(eb_hash, voter_id)` style inputs. No
  `from_entropy` / `thread_rng`.
- Tracing (`info!`, `warn!`) is allowed; it's a side-effect-free sink
  from the state machine's perspective.

### 2. Effect emission, not callbacks

State machines mutate themselves and return `Vec<Effect>`. The caller's
I/O wrapper drains the vector and dispatches each effect to the right
channel (network, validator, telemetry).

- **Public methods**: return `Vec<PraosEffect>` / `Vec<LeiosEffect>`.
- **Internal helpers** (private `*_internal` methods): take
  `fx: &mut Vec<…>` to append to the running batch — avoids allocating
  per call inside the state machine.
- Don't add a callback / closure parameter to "report something back."
  Add a new effect variant.

### 3. Determinism

`sim-rs` replays runs from a seed. shared-consensus must not introduce
non-deterministic ordering.

- `BTreeMap` / `BTreeSet` everywhere. No `HashMap` iteration in hot
  paths.
- Existing `HashMap` usage is keyed on EB hashes and only iterated
  during pure quorum checks where order doesn't change the outcome —
  audit before adding any new `HashMap`.
- Effect order in `Elections::on_slot` is part of the contract:
  every `EligibleToVote` (sorted by `eb_hash`) first, then every
  `Expired`. Don't shuffle.

### 4. Format-agnostic

Block bodies, headers, vote bodies cross the crate boundary as opaque
`Vec<u8>`. CBOR parsing is the I/O wrapper's job.

- `CachedBlock` carries `header: Vec<u8>, body: Vec<u8>`.
- `LeiosEffect::EmitVote` carries logical args (`emit_pv: bool`,
  `npv_signature: Option<Vec<u8>>`); the wrapper builds the wire body.
- The exception is `types.rs` — `Point` and `Tip` carry their own
  `minicbor` impls because their wire format is fixed across all
  Cardano implementations. Don't add more wire types here.

### 5. Comments stay consumer-neutral

Don't name `net-node` or `sim-rs` (or any future consumer) in
shared-consensus doc comments. Describe the contract from this crate's
own perspective — "the I/O wrapper" / "the caller", never "net-node
uses this for X."

## Module map

```
lib.rs              re-exports Point, Tip, PeerId, CommitteeSelection, StakeEntry

types.rs            Point, Tip with minicbor codec
peer.rs             PeerId(u64) wrapper
config.rs           CommitteeSelection enum, StakeEntry
pipeline.rs         PipelineConfig — phase math (Voting/CertEligible/Expired)
committee.rs        Committee selection (WfaLs, EveryoneVotes, StakeCentile), NPV lottery
lottery.rs          Praos f_block stake-weighted threshold formula
aggregation.rs      record_vote, QuorumFormed
bitmap.rs           sparse BTreeMap<u16, u64> for MsgLeiosBlockTxsRequest
chain_tree.rs       in-memory chain DAG, best-tip selection, prune_below
peer_chain.rs       per-peer announced fragment (cap-bounded VecDeque)
fetch.rs            per-channel fetch policies + CandidateTracker + PeerRtt
elections.rs        Elections sans-IO state machine — slot ticks → SlotEffect
praos.rs            PraosState — chain state + selection → PraosEffect
leios.rs            LeiosState — EB voting + tx fetch state → LeiosEffect
mempool.rs          MempoolState — bounded tx pool + EB-pinned bodies
                    → MempoolEffect
production.rs       BodyPath::decide — inline-RB vs EB vs empty-for-safety
behaviour/          Pluggable per-node hooks (lazy voter, RB equivocator,
                    …); see behaviour/README.md
```

## Behaviours

Each host state machine owns an `Arc<Mutex<Box<dyn Behaviour>>>` that
adversarial / experimental variants slot into. The trait surface (four
hook kinds — reactive, decision, strategy, notification — plus a
per-peer outbound transform), the registry that materialises a
[`BehaviourSpec`] from config, the composition rules, and the recipe
for shipping a new behaviour all live in
[`src/behaviour/README.md`](src/behaviour/README.md).

When adding or modifying a behaviour, the rules above still apply —
no `Instant::now()`, no `HashMap` iteration, no `thread_rng`. Random
behaviours take a `u64` seed at construction and feed it through
`blake2b_simd` along with the per-decision key (peer id, slot, …).

## When adding a new method

1. Decide: pure query, or state mutation?
2. State mutation → return `Vec<Effect>` (or `()` if no effects ever).
3. Need wall-clock? Take `now: Instant` as a parameter.
4. Need iteration? `BTreeMap`/`BTreeSet`, not `HashMap`/`HashSet`.
5. Need wire bytes in/out? Carry as `Vec<u8>`; never decode CBOR.
6. Add a unit test that constructs the state, calls the method, and
   asserts on the returned effects.

## Tests

`cargo test` runs the full unit-test suite. There are **no integration
tests** — every state machine is tested directly in its own module's
`#[cfg(test)] mod tests` block. Mocking is trivial because effects are
just enum variants you compare against.

Common test helpers in each module:

- `elections.rs::test_pipeline()` — minimal `PipelineConfig`.
- `aggregation.rs::make_election(slot)` — fresh `EbElection` for the
  given slot.
- `praos.rs::install_validated_block(state, slot, seed, block_no, prev_seed)` —
  pre-populate `chain_tree + block_cache + validated` to skip driving
  every scenario through the public API.
- `leios.rs::elections_for(node_id)`, `cfg(persistent_seats)` — minimal
  `Elections` and `VotingConfig` builders.

## Building

```
cd /home/prc/leios-net-rs/shared-rs
cargo build       # workspace build
cargo test        # all unit tests (each module has its own mod tests)
cargo clippy --all-targets -- -D warnings
```

When working from net-rs's or sim-rs's worktree, shared-consensus
writes need `dangerouslyDisableSandbox: true` because the crate lives
outside their project sandboxes.

## Sequencing context

shared-consensus was first extracted from `net-rs` as `con-rs` (branch
`prc/con-rs`), then moved under the `shared-rs/` workspace so that
other consumer-neutral crates (e.g. `tcp-model`) could share its
top-level. `sim-rs` adoption is in progress — it required unifying
on the wFA voting model (sim-rs originally used a per-voter VRF trial
schedule). Treat the crate's API as still-shaping; net-rs's needs have
priority where they conflict.

Future trait surface (deferred): `Mempool`, `Ledger`. Both will be
dyn-trait boundaries that each consumer implements with its own
storage model. Don't pre-design these — add them when the second
consumer arrives.
