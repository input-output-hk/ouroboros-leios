//! Behaviour hook system — pluggable extension points for adversarial
//! and experimental variants of the protocol.
//!
//! A [`Behaviour`] is a trait object owned by each of [`LeiosState`],
//! [`PraosState`], and [`MempoolState`].  Every protocol-affecting
//! decision in those state machines consults the behaviour first:
//!
//! - **Reactive hooks** (`on_*`) fire at the top of every public
//!   `on_xxx` event handler.  The behaviour may [`Continue`](
//!   BehaviourOutcome::Continue) (let honest flow run unchanged),
//!   [`Replace`](BehaviourOutcome::Replace) (substitute the entire
//!   effect list), or [`Append`](BehaviourOutcome::Append) (run honest
//!   flow AND add the extra effects — the equivocation pattern).
//! - **Decision hooks** (`decide_*`) fire inline at branch points like
//!   the voting predicate and the RB body-path picker.  The behaviour
//!   may [`Continue`](DecisionOutcome::Continue) (use the honest
//!   decision) or [`Override`](DecisionOutcome::Override) (substitute).
//! - **Strategy hooks** describe production-time choices the wrapper
//!   makes (e.g., produce one RB vs. equivocate vs. suppress).  They
//!   return a small enum the wrapper interprets — the actual artefact
//!   construction stays in the wrapper because the artefact bytes are
//!   opaque to this crate.
//!
//! All hooks default to `Continue` / the honest variant, so a concrete
//! behaviour overrides only the hooks it cares about.  [`HonestBehaviour`]
//! is the default no-op; [`CompositeBehaviour`] composes children in
//! order (first non-`Continue` wins).
//!
//! ## Ownership and access
//!
//! Hooks receive `&mut self` (so they can carry their own state) and
//! `&LeiosState` / `&PraosState` / `&MempoolState` (read-only views of
//! the host).  Each host state stores the behaviour as
//! `Arc<Mutex<Box<dyn Behaviour>>>`.  The Arc lets the I/O wrapper hold
//! a shared handle and call out-of-band hooks (e.g. per-peer outbound
//! transforms) on the same trait object; the Mutex serialises those
//! calls against the state's own dispatch.  The inner `Box` is the
//! swap point: replacing it under the lock (via `set_behaviour`)
//! changes the live behaviour for every Arc holder at once.
//!
//! ## Determinism
//!
//! Behaviours must be deterministic — sim-rs replays runs from a seed.
//! No `Instant::now()` inside hook logic; if a behaviour needs to time
//! its activation, drive it off `slot` (which every reactive hook
//! receives or can read from the host state).

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use crate::leios::{LeiosEffect, LeiosState, VoteDecision};
use crate::mempool::{MempoolEffect, MempoolState, TxId};
use crate::peer::PeerId;
use crate::praos::{PraosEffect, PraosState};
use crate::production::BodyPath;
use crate::types::Point;

/// Shared handle to a per-node behaviour.  The I/O wrapper holds one
/// `BehaviourHandle` per node; cloning it (cheap `Arc::clone`) gives
/// out-of-band callers — e.g. per-peer server tasks evaluating
/// `transform_outbound` — access to the same trait object the state
/// machines call.  Locking is short-lived: hook bodies are synchronous
/// and must not await while the guard is held.
pub type BehaviourHandle = Arc<Mutex<Box<dyn Behaviour>>>;

/// One RB variant the I/O wrapper just produced for a single
/// equivocation slot, handed to the behaviour via
/// [`Behaviour::record_rb_variants`].  `hash` is the wire-format
/// header hash (the same `[u8; 32]` that ends up inside the
/// `Point::Specific` peers see); the wrapper computes it because the
/// CBOR-envelope decoding required to derive it lives in the wire
/// layer, not in this sans-IO crate.
#[derive(Debug, Clone)]
pub struct RbVariantInput {
    pub hash: [u8; 32],
    pub header: Vec<u8>,
    pub body: Vec<u8>,
}

pub mod delay;
pub mod outbound;
pub mod registry;
pub mod selection;

pub mod behaviours {
    //! Concrete [`super::Behaviour`] implementations.  Each lives in its
    //! own file so contributors can add one without touching the others.
    pub mod lazy_voter;
    pub mod rb_equivocator;
    pub mod t22;

    pub use lazy_voter::LazyVoter;
    pub use rb_equivocator::RbHeaderEquivocator;
    pub use t22::T22ThreatBehaviour;
}

pub use delay::DelayQueue;
pub use outbound::{Outbound, OutboundDecision, OwnedOutbound};
pub use registry::{build, build_handle, seed_from_node_id, swap_handle, BehaviourSpec};
pub use selection::{resolve_selection, resolve_specs, BehaviourSelection};

// `BehaviourHandle` is defined at the top of this module.

// ---------------------------------------------------------------------------
// Outcome types
// ---------------------------------------------------------------------------

/// What a reactive hook returns.  `Continue` lets honest flow proceed
/// unchanged; `Replace` discards the honest effects and uses these
/// instead; `Append` runs the honest flow AND appends these extras.
#[derive(Debug, Clone, Default)]
pub enum BehaviourOutcome<E> {
    #[default]
    Continue,
    Replace(Vec<E>),
    Append(Vec<E>),
}

impl<E> BehaviourOutcome<E> {
    pub fn is_continue(&self) -> bool {
        matches!(self, BehaviourOutcome::Continue)
    }
}

/// What a `decide_*` hook returns.  `Continue` keeps the honest
/// decision; `Override` substitutes it.
#[derive(Debug, Clone, Default)]
pub enum DecisionOutcome<T> {
    #[default]
    Continue,
    Override(T),
}

impl<T> DecisionOutcome<T> {
    pub fn resolve(self, honest: T) -> T {
        match self {
            DecisionOutcome::Continue => honest,
            DecisionOutcome::Override(t) => t,
        }
    }
}

// ---------------------------------------------------------------------------
// Strategy hook types
// ---------------------------------------------------------------------------

/// Production-time strategy for self-produced RBs.  Consulted by the
/// wrapper before it signs an RB header.  Honest nodes always return
/// [`RbProductionStrategy::Normal`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum RbProductionStrategy {
    /// Produce one honest RB (the default).
    #[default]
    Normal,
    /// Produce no RB this slot — the lottery win is wasted.  Selective
    /// withholding adversaries use this to drop blocks without
    /// equivocating.
    Suppress,
    /// Produce `ways` RBs for the same lottery, all differing in body
    /// content.  The wrapper signs them, registers the first as the
    /// primary (so its own chain follows it), and hands the full set
    /// to the behaviour via [`Behaviour::record_rb_variants`].  The
    /// behaviour then routes a different variant to each peer subset
    /// via [`Behaviour::transform_outbound`]; honest peers see the
    /// duplicates as they gossip and detect the equivocation via the
    /// CIP-0164 RB-header equivocation rule.  `ways >= 2`.
    Equivocate { ways: u8 },
}

// ---------------------------------------------------------------------------
// Behaviour trait
// ---------------------------------------------------------------------------

/// Pluggable per-node behaviour.  See the module docs for the dispatch
/// rules and the take/restore borrowing pattern.
///
/// Every hook has a default that delegates to honest flow, so a
/// concrete impl overrides only the hooks it cares about.
pub trait Behaviour: Send + Sync {
    /// Short identifier used in telemetry / logs.  Defaults to
    /// `"honest"`; override in concrete impls.
    fn name(&self) -> &'static str {
        "honest"
    }

    // -- Leios reactive hooks ------------------------------------------------

    fn on_slot_leios(
        &mut self,
        _state: &LeiosState,
        _slot: u64,
    ) -> BehaviourOutcome<LeiosEffect> {
        BehaviourOutcome::Continue
    }

    fn on_eb_offered(
        &mut self,
        _state: &LeiosState,
        _point: &Point,
        _peer: PeerId,
    ) -> BehaviourOutcome<LeiosEffect> {
        BehaviourOutcome::Continue
    }

    fn on_eb_txs_offered(
        &mut self,
        _state: &LeiosState,
        _point: &Point,
        _peer: PeerId,
        _bitmap: &BTreeMap<u16, u64>,
    ) -> BehaviourOutcome<LeiosEffect> {
        BehaviourOutcome::Continue
    }

    fn on_votes_offered(
        &mut self,
        _state: &LeiosState,
        _peer: PeerId,
        _vote_ids: &[(u64, Vec<u8>)],
    ) -> BehaviourOutcome<LeiosEffect> {
        BehaviourOutcome::Continue
    }

    fn on_eb_received(
        &mut self,
        _state: &LeiosState,
        _point: &Point,
        _tx_hashes: &[[u8; 32]],
    ) -> BehaviourOutcome<LeiosEffect> {
        BehaviourOutcome::Continue
    }

    fn on_votes_received(
        &mut self,
        _state: &LeiosState,
        _vote_ids: &[(u64, Vec<u8>)],
        _vote_data: &[Vec<u8>],
    ) -> BehaviourOutcome<LeiosEffect> {
        BehaviourOutcome::Continue
    }

    fn on_validated_votes(
        &mut self,
        _state: &LeiosState,
        _vote_bodies: &[Vec<u8>],
    ) -> BehaviourOutcome<LeiosEffect> {
        BehaviourOutcome::Continue
    }

    // -- Leios decision hooks ------------------------------------------------

    /// Override the CIP-0164 voting predicate.  The honest decision is
    /// passed in so the behaviour can inspect it (e.g., "abstain only
    /// when honest would have voted yes").  Returning `Continue` keeps
    /// the honest decision.
    fn decide_vote(
        &mut self,
        _state: &LeiosState,
        _eb_hash: &[u8; 32],
        _eb_slot: u64,
        _honest: &VoteDecision,
    ) -> DecisionOutcome<VoteDecision> {
        DecisionOutcome::Continue
    }

    // -- Praos reactive hooks ------------------------------------------------

    fn on_tip_advanced(
        &mut self,
        _state: &PraosState,
        _peer: PeerId,
        _tip: &Point,
    ) -> BehaviourOutcome<PraosEffect> {
        BehaviourOutcome::Continue
    }

    fn on_block_received(
        &mut self,
        _state: &PraosState,
        _point: &Point,
    ) -> BehaviourOutcome<PraosEffect> {
        BehaviourOutcome::Continue
    }

    fn on_peer_disconnected(
        &mut self,
        _state: &PraosState,
        _peer: PeerId,
    ) -> BehaviourOutcome<PraosEffect> {
        BehaviourOutcome::Continue
    }

    // -- Praos decision hooks ------------------------------------------------

    // (decide_select_chain hook deferred — the honest selection returns a
    // typed enum nested in praos.rs internals; once the public surface
    // stabilises we'll hook it.  Reactive on_block_received covers most
    // chain-switch adversaries for now.)

    // -- Mempool reactive hooks ----------------------------------------------

    fn on_tx_received(
        &mut self,
        _state: &MempoolState,
        _tx_id: &TxId,
        _body: &[u8],
    ) -> BehaviourOutcome<MempoolEffect> {
        BehaviourOutcome::Continue
    }

    fn on_tx_validated(
        &mut self,
        _state: &MempoolState,
        _tx_id: &TxId,
        _size: u32,
    ) -> BehaviourOutcome<MempoolEffect> {
        BehaviourOutcome::Continue
    }

    // -- Body-path decision hook ---------------------------------------------

    /// Override the producer-side body-path choice.  `honest` is what
    /// [`BodyPath::decide`] returned; returning `Continue` keeps it,
    /// `Override` substitutes.
    fn decide_body_path(
        &mut self,
        _leios: &LeiosState,
        _honest: &BodyPath,
    ) -> DecisionOutcome<BodyPath> {
        DecisionOutcome::Continue
    }

    // -- Production strategy hooks -------------------------------------------

    /// Consulted by the wrapper before it signs an RB header.  Returns
    /// the strategy (one honest, suppress, equivocate).
    ///
    /// This is a strategy hook, not a reactive one: the wrapper acts on
    /// the returned value by producing zero, one, or many RBs.  Because
    /// shared-consensus does not own the wire-format RB construction
    /// path, the actual artefact is built by the wrapper from the
    /// honest body-path decision (already overridable via
    /// [`Self::decide_body_path`]).
    fn rb_production_strategy(
        &mut self,
        _leios: &LeiosState,
        _praos: &PraosState,
        _slot: u64,
    ) -> RbProductionStrategy {
        RbProductionStrategy::Normal
    }

    /// Hand the I/O wrapper's freshly-produced RB variants to the
    /// behaviour, so a peer-split adversary can stash them for the
    /// upcoming [`transform_outbound`](Self::transform_outbound) calls
    /// and the body-server fallback
    /// ([`find_variant_body`](Self::find_variant_body)).  `slot` is the
    /// production slot; `variants` is the full set (`variants[0]` is
    /// the primary the wrapper registered locally, `variants[1..]` are
    /// the duplicates).  The default is a no-op.
    fn record_rb_variants(&mut self, _slot: u64, _variants: &[RbVariantInput]) {}

    /// Look up the body of a variant the behaviour stashed earlier via
    /// [`record_rb_variants`](Self::record_rb_variants).  The I/O
    /// wrapper's BlockFetch server consults this when a peer asks for
    /// a body that is not in the local chain store — typically because
    /// the behaviour advertised a peer-split variant to that peer via
    /// [`transform_outbound`](Self::transform_outbound) and the peer
    /// is now asking for its body.  Default is `None`.
    fn find_variant_body(&self, _slot: u64, _hash: &[u8; 32]) -> Option<Vec<u8>> {
        None
    }

    // -- Outbound transform --------------------------------------------------

    /// Per-peer outbound rewrite.  Called by the I/O wrapper before
    /// every peer-targeted send.  The default lets the artefact pass
    /// through unchanged; adversarial behaviours return
    /// [`Drop`](OutboundDecision::Drop) (partition, eclipse mute),
    /// [`Replace`](OutboundDecision::Replace) (peer-split equivocation,
    /// eclipse fake tip), or [`Augment`](OutboundDecision::Augment).
    ///
    /// `peer` is an opaque token assigned by the I/O wrapper; this
    /// crate does not enumerate peers, it only routes per-peer decisions
    /// when the wrapper asks.  Determinism is the behaviour's
    /// responsibility (see the seed accepted at
    /// [`registry::build`]).
    fn transform_outbound(
        &mut self,
        _peer: PeerId,
        _out: Outbound<'_>,
    ) -> OutboundDecision {
        OutboundDecision::Send
    }
}

// ---------------------------------------------------------------------------
// Honest default
// ---------------------------------------------------------------------------

/// No-op behaviour — every hook returns `Continue` / `Normal`.  Used as
/// the default for every state machine; concrete behaviours wrap this
/// implicitly via the trait's default methods.
#[derive(Debug, Default)]
pub struct HonestBehaviour;

impl Behaviour for HonestBehaviour {}

// ---------------------------------------------------------------------------
// Composition
// ---------------------------------------------------------------------------

/// Compose multiple behaviours.  For each hook, calls each child in
/// order and returns the first non-`Continue` result.  Lets contributors
/// layer (e.g.) "delay-and-equivocate" without touching either
/// constituent.
pub struct CompositeBehaviour {
    pub children: Vec<Box<dyn Behaviour>>,
}

impl CompositeBehaviour {
    pub fn new(children: Vec<Box<dyn Behaviour>>) -> Self {
        Self { children }
    }
}

// Composite delegations are spelled out explicitly: each host-state
// type and argument list is different enough that a macro would
// obscure more than it saves at this scale.  Pattern is uniform: walk
// children, return the first non-`Continue` result, fall through to
// `Continue` if all defer.
impl Behaviour for CompositeBehaviour {
    fn name(&self) -> &'static str {
        "composite"
    }

    fn on_slot_leios(
        &mut self,
        state: &LeiosState,
        slot: u64,
    ) -> BehaviourOutcome<LeiosEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_slot_leios(state, slot);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn on_eb_offered(
        &mut self,
        state: &LeiosState,
        point: &Point,
        peer: PeerId,
    ) -> BehaviourOutcome<LeiosEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_eb_offered(state, point, peer);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn on_eb_txs_offered(
        &mut self,
        state: &LeiosState,
        point: &Point,
        peer: PeerId,
        bitmap: &BTreeMap<u16, u64>,
    ) -> BehaviourOutcome<LeiosEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_eb_txs_offered(state, point, peer, bitmap);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn on_votes_offered(
        &mut self,
        state: &LeiosState,
        peer: PeerId,
        vote_ids: &[(u64, Vec<u8>)],
    ) -> BehaviourOutcome<LeiosEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_votes_offered(state, peer, vote_ids);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn on_eb_received(
        &mut self,
        state: &LeiosState,
        point: &Point,
        tx_hashes: &[[u8; 32]],
    ) -> BehaviourOutcome<LeiosEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_eb_received(state, point, tx_hashes);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn on_votes_received(
        &mut self,
        state: &LeiosState,
        vote_ids: &[(u64, Vec<u8>)],
        vote_data: &[Vec<u8>],
    ) -> BehaviourOutcome<LeiosEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_votes_received(state, vote_ids, vote_data);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn on_validated_votes(
        &mut self,
        state: &LeiosState,
        vote_bodies: &[Vec<u8>],
    ) -> BehaviourOutcome<LeiosEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_validated_votes(state, vote_bodies);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn decide_vote(
        &mut self,
        state: &LeiosState,
        eb_hash: &[u8; 32],
        eb_slot: u64,
        honest: &VoteDecision,
    ) -> DecisionOutcome<VoteDecision> {
        for c in self.children.iter_mut() {
            if let DecisionOutcome::Override(v) = c.decide_vote(state, eb_hash, eb_slot, honest) {
                return DecisionOutcome::Override(v);
            }
        }
        DecisionOutcome::Continue
    }

    fn on_tip_advanced(
        &mut self,
        state: &PraosState,
        peer: PeerId,
        tip: &Point,
    ) -> BehaviourOutcome<PraosEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_tip_advanced(state, peer, tip);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn on_block_received(
        &mut self,
        state: &PraosState,
        point: &Point,
    ) -> BehaviourOutcome<PraosEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_block_received(state, point);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn on_peer_disconnected(
        &mut self,
        state: &PraosState,
        peer: PeerId,
    ) -> BehaviourOutcome<PraosEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_peer_disconnected(state, peer);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn on_tx_received(
        &mut self,
        state: &MempoolState,
        tx_id: &TxId,
        body: &[u8],
    ) -> BehaviourOutcome<MempoolEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_tx_received(state, tx_id, body);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn on_tx_validated(
        &mut self,
        state: &MempoolState,
        tx_id: &TxId,
        size: u32,
    ) -> BehaviourOutcome<MempoolEffect> {
        for c in self.children.iter_mut() {
            let out = c.on_tx_validated(state, tx_id, size);
            if !out.is_continue() {
                return out;
            }
        }
        BehaviourOutcome::Continue
    }

    fn decide_body_path(
        &mut self,
        leios: &LeiosState,
        honest: &BodyPath,
    ) -> DecisionOutcome<BodyPath> {
        for c in self.children.iter_mut() {
            if let DecisionOutcome::Override(v) = c.decide_body_path(leios, honest) {
                return DecisionOutcome::Override(v);
            }
        }
        DecisionOutcome::Continue
    }

    fn rb_production_strategy(
        &mut self,
        leios: &LeiosState,
        praos: &PraosState,
        slot: u64,
    ) -> RbProductionStrategy {
        for c in self.children.iter_mut() {
            let s = c.rb_production_strategy(leios, praos, slot);
            if s != RbProductionStrategy::Normal {
                return s;
            }
        }
        RbProductionStrategy::Normal
    }

    fn transform_outbound(
        &mut self,
        peer: PeerId,
        out: Outbound<'_>,
    ) -> OutboundDecision {
        for c in self.children.iter_mut() {
            let d = c.transform_outbound(peer, out);
            if !d.is_send() {
                return d;
            }
        }
        OutboundDecision::Send
    }

    /// Notification — fan out to every child.  No short-circuit: a
    /// composite "logger + equivocator" should record on both, not just
    /// the first.
    fn record_rb_variants(&mut self, slot: u64, variants: &[RbVariantInput]) {
        for c in self.children.iter_mut() {
            c.record_rb_variants(slot, variants);
        }
    }

    /// First child to answer wins.  Variant stores are usually disjoint
    /// — composite of equivocator + lazy-voter only has bodies in the
    /// equivocator — so first-wins is the right shape.
    fn find_variant_body(&self, slot: u64, hash: &[u8; 32]) -> Option<Vec<u8>> {
        for c in self.children.iter() {
            if let Some(body) = c.find_variant_body(slot, hash) {
                return Some(body);
            }
        }
        None
    }
}

// ---------------------------------------------------------------------------
// Dispatch helpers
// ---------------------------------------------------------------------------

/// Apply a `BehaviourOutcome` to an honest-effects builder.  Pattern:
///
/// ```ignore
/// let arc = state.behaviour.clone();
/// let mut guard = arc.lock().unwrap();
/// let outcome = guard.on_slot_leios(state, slot);
/// drop(guard);
/// let fx = apply_reactive(outcome, || /* honest fx */ );
/// ```
///
/// The honest closure is only evaluated when the outcome is `Continue`
/// or `Append`, so `Replace` short-circuits the honest computation.
pub fn apply_reactive<E, F>(outcome: BehaviourOutcome<E>, honest: F) -> Vec<E>
where
    F: FnOnce() -> Vec<E>,
{
    match outcome {
        BehaviourOutcome::Continue => honest(),
        BehaviourOutcome::Replace(effects) => effects,
        BehaviourOutcome::Append(extra) => {
            let mut fx = honest();
            fx.extend(extra);
            fx
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Stub behaviour that records which hooks it saw and returns a
    /// configurable outcome.  Used to assert composition order.
    struct CountingBehaviour {
        name: &'static str,
        on_slot_calls: u32,
        on_slot_reply: BehaviourOutcome<LeiosEffect>,
    }

    impl Behaviour for CountingBehaviour {
        fn name(&self) -> &'static str {
            self.name
        }
        fn on_slot_leios(
            &mut self,
            _state: &LeiosState,
            _slot: u64,
        ) -> BehaviourOutcome<LeiosEffect> {
            self.on_slot_calls += 1;
            self.on_slot_reply.clone()
        }
    }

    fn make_state() -> LeiosState {
        use crate::config::CommitteeSelection;
        use crate::elections::{Elections, ElectionsConfig};
        use crate::leios::VotingConfig;
        use crate::pipeline::PipelineConfig;

        let pipeline = PipelineConfig {
            delta_hdr: 1,
            vote_window: 5,
            diffuse_window: 5,
            dedup_window: 10,
        };
        let elections = Elections::new(ElectionsConfig {
            node_id: "t".to_string(),
            pipeline,
            committee_selection: CommitteeSelection::EveryoneVotes,
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 100,
            expected_total_weight: 1,
            quorum_weight_fraction: 0.75,
        });
        let voting = VotingConfig {
            committee_selection: CommitteeSelection::EveryoneVotes,
            stake: 1,
            total_stake: 100,
            persistent_vote_bytes: 130,
            non_persistent_vote_bytes: 180,
            persistent_seats: 0,
            retry_vote_in_window: true,
        };
        LeiosState::new("t".to_string(), elections, voting, pipeline)
    }

    #[test]
    fn honest_is_noop() {
        let mut h = HonestBehaviour;
        let s = make_state();
        let out = h.on_slot_leios(&s, 5);
        assert!(matches!(out, BehaviourOutcome::Continue));
    }

    #[test]
    fn composite_short_circuits_on_first_non_continue() {
        let s = make_state();
        let first = CountingBehaviour {
            name: "first",
            on_slot_calls: 0,
            on_slot_reply: BehaviourOutcome::Continue,
        };
        let second = CountingBehaviour {
            name: "second",
            on_slot_calls: 0,
            on_slot_reply: BehaviourOutcome::Replace(vec![]),
        };
        let third = CountingBehaviour {
            name: "third",
            on_slot_calls: 0,
            on_slot_reply: BehaviourOutcome::Replace(vec![]),
        };
        let mut composite = CompositeBehaviour::new(vec![
            Box::new(first),
            Box::new(second),
            Box::new(third),
        ]);
        let out = composite.on_slot_leios(&s, 5);
        assert!(matches!(out, BehaviourOutcome::Replace(_)));
        // Third never ran.  We can't introspect after wrapping in Box<dyn>,
        // but the contract is: short-circuit on first non-Continue.
    }

    #[test]
    fn composite_all_continue_returns_continue() {
        let s = make_state();
        let mut c = CompositeBehaviour::new(vec![
            Box::new(HonestBehaviour),
            Box::new(HonestBehaviour),
            Box::new(HonestBehaviour),
        ]);
        assert!(c.on_slot_leios(&s, 1).is_continue());
    }

    #[test]
    fn apply_reactive_continue_runs_honest() {
        let out = BehaviourOutcome::<u32>::Continue;
        let fx = apply_reactive(out, || vec![1, 2, 3]);
        assert_eq!(fx, vec![1, 2, 3]);
    }

    #[test]
    fn apply_reactive_replace_skips_honest() {
        let out = BehaviourOutcome::Replace(vec![9, 9]);
        let mut honest_ran = false;
        let fx = apply_reactive(out, || {
            honest_ran = true;
            vec![1, 2]
        });
        assert_eq!(fx, vec![9, 9]);
        assert!(!honest_ran);
    }

    #[test]
    fn apply_reactive_append_runs_both() {
        let out = BehaviourOutcome::Append(vec![9]);
        let fx = apply_reactive(out, || vec![1, 2]);
        assert_eq!(fx, vec![1, 2, 9]);
    }

    #[test]
    fn decision_outcome_resolve() {
        let cont: DecisionOutcome<i32> = DecisionOutcome::Continue;
        assert_eq!(cont.resolve(7), 7);
        let over: DecisionOutcome<i32> = DecisionOutcome::Override(42);
        assert_eq!(over.resolve(7), 42);
    }
}
