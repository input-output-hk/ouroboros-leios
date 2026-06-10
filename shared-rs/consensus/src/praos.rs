//! Praos longest-chain consensus state machine.
//!
//! `PraosState` owns this node's view of the chain world: its adopted
//! chain tree, block cache, per-peer announced fragments, validator-
//! queue projection, and orphan / in-flight tracking.  It is sans-IO:
//! every public method either mutates state and returns a
//! `Vec<PraosEffect>` describing what the caller's I/O layer should
//! dispatch — fetch a block range, re-intersect with a peer, hand a
//! block to the validator, inject into the chain store — or returns a
//! pure query result.
//!
//! Block bodies and headers are carried as opaque `Vec<u8>`.  CBOR
//! parsing happens at the I/O boundary; this crate never interprets the
//! bytes.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use serde::Serialize;
use tracing::{debug, info, warn};

use crate::chain_tree::{is_better_tip, ChainTree, ChainTreeEntry};
use crate::fetch::{BlockFetchPolicy, LowestRttFirst, PeerRtt, UniformRtt};
use crate::peer::PeerId;
use crate::peer_chain::{PeerChain, PeerChainEntry};
use crate::types::Point;

/// How long an in-flight fetch entry remains "active" before being
/// considered stale and eligible for retry.  The coordinator may
/// silently drop a fetch (e.g. no connected peer has the requested
/// point), so we need a recovery path: if no body arrives within this
/// window, allow a fresh fetch.
pub const IN_FLIGHT_TTL: Duration = Duration::from_secs(15);

/// Minimum interval between chain_tree gap-bridge fetches anchored at the
/// same adopted tip.  Without it, an advancing `best_tip` (the live peer
/// keeps producing) defeats the per-block in-flight dedup — `gap_point`
/// changes every tick, so the bridge re-issues the entire
/// `[adopted_tip → best_tip]` range continuously, amplifying block
/// traffic.  Resets as soon as the adopted tip advances (real progress).
pub const BRIDGE_COOLDOWN: Duration = Duration::from_secs(10);

/// After a peer is classified as `OrphanCandidate`, this much time must
/// pass before it is reconsidered for chain selection.  Caps the
/// orphan-cascade rate at 1/sec per peer even when re-intersection
/// round-trips are millisecond-scale.
pub const ORPHAN_COOLDOWN: Duration = Duration::from_secs(1);

/// After a peer fails to deliver a fetched block (NoBlocks, mux error,
/// timeout, malformed body), this much time must pass before chain
/// selection considers it again.  Without this, `on_block_fetch_failed`
/// re-runs `select_chain_once` immediately and picks the same peer
/// (because nothing has changed about its announced fragment), which
/// busy-loops at microsecond cadence and saturates disk I/O with the
/// fetch-and-fail log pair.  Routing decisions are the fetch policy's
/// job; this cooldown just keeps a known-bad peer out of the running
/// long enough for a different one to be picked.
pub const BLOCK_FETCH_COOLDOWN: Duration = Duration::from_secs(2);

/// How long validation must be frozen with peers offering strictly-better
/// tips before a stuck-rollup WARN is considered.  Catches genuine wedges
/// without crying wolf during the short pauses between bursts of
/// validation.
pub const STUCK_THRESHOLD: Duration = Duration::from_secs(30);

/// Minimum interval between stuck-rollup WARNs.  The per-event INFO logs
/// already fire ~1/sec; this rollup is a synthesised once-per-minute
/// summary aimed at an operator skimming logs.
pub const STUCK_WARNING_INTERVAL: Duration = Duration::from_secs(60);

/// Per-peer cooldown between non-contiguous-header WARNs emitted at
/// ChainSync ingress.  The signal is "upstream is forwarding a gappy
/// chain"; reporting every individual gap floods the log without adding
/// information.
pub const GAP_WARNING_INTERVAL: Duration = Duration::from_secs(10);

/// Snapshot of [`PraosState`]'s internal collection sizes plus byte
/// estimates for the equivocation tracking maps.  Emitted per slot via
/// telemetry so leak rate can be plotted independently of run length.
#[derive(Debug, Clone, Serialize)]
pub struct PraosStateSizes {
    pub chain_tree: usize,
    pub block_cache: usize,
    pub validated: usize,
    pub in_flight: usize,
    pub in_flight_validation: usize,
    pub self_produced: usize,
    pub peer_chains: usize,
    pub peer_chain_total: usize,
    pub peer_chain_max: usize,
    pub header_first_seen: usize,
    pub header_hashes_by_slot_issuer: usize,
    pub issuer_hashes_total: usize,
    pub equivocating_rb_slots: usize,
    pub orphan_cooldown: usize,
    pub block_fetch_cooldown: usize,
    /// Rough byte estimate covering `header_hashes_by_slot_issuer` (outer +
    /// inner) and `equivocating_rb_slots`.  Multiplies counts by per-entry
    /// constants — not exact heap usage.
    pub equivocation_bytes_estimate: usize,
}

// ---------------------------------------------------------------------------
// Effect type
// ---------------------------------------------------------------------------

/// Logical action that the I/O wrapper should perform.  PraosState emits
/// these as a side-channel to its mutations; the wrapper drains and
/// dispatches each to the appropriate channel (network commands,
/// validator submissions).  Header / body bodies are opaque bytes; the
/// wrapper rehydrates them into wire types as it dispatches.
#[derive(Debug, Clone)]
pub enum PraosEffect {
    /// Request a contiguous block range from the network.  `peers` is
    /// the [`BlockFetchPolicy`]'s ranked picks among the candidates
    /// known to the chain-tracking state — the I/O wrapper dispatches
    /// one fetch per peer in the list (so a `BroadcastN` policy will
    /// produce a fan-out, while `LowestRttFirst` gives a single peer).
    /// An empty `peers` means no candidate is known yet; the wrapper
    /// can drop the effect or retry later.
    FetchBlockRange {
        from: Point,
        to: Point,
        peers: Vec<PeerId>,
    },
    /// Ask the coordinator to re-run the ChainSync intersection
    /// negotiation with this peer.
    ReIntersect { peer_id: PeerId },
    /// Publish a validated block to the network's responder-side
    /// chain store (so peers fetching from us can get it).
    InjectBlock {
        point: Point,
        header: Vec<u8>,
        body: Vec<u8>,
        block_no: u64,
    },
    /// Roll the chain store back to `target`.  `Origin` clears it.
    InjectRollback { target: Point },
    /// Submit a block to the ledger validator (`LedgerCommand::Apply`).
    ValidatorApply {
        point: Point,
        body: Vec<u8>,
        prev_hash: Option<[u8; 32]>,
    },
    /// Submit a rollback to the ledger validator
    /// (`LedgerCommand::Rollback`).
    ValidatorRollback { target: Point },
}

// ---------------------------------------------------------------------------
// Cached block
// ---------------------------------------------------------------------------

/// A block we possess (fetched from a peer or self-produced).  Header
/// and body are raw CBOR bytes — the wire types live in net-core and
/// are reconstructed by the I/O wrapper when an effect dispatches them.
#[derive(Debug, Clone)]
pub struct CachedBlock {
    pub point: Point,
    pub block_no: u64,
    pub prev_hash: Option<[u8; 32]>,
    pub header: Vec<u8>,
    pub body: Vec<u8>,
    /// EB hash this block's header announces (CIP-0164 Leios extension).
    /// `None` for opaque or pre-Leios headers; the I/O wrapper sets this
    /// when it parses the header.
    pub announced_eb_hash: Option<[u8; 32]>,
    /// Whether this block's header certifies the parent RB's
    /// announced EB (CIP-0164 Leios extension).  The EB being
    /// certified is resolved via [`PraosState::parent_announced_eb_for_cert`].
    pub certified_eb: bool,
}

// ---------------------------------------------------------------------------
// Selection result types
// ---------------------------------------------------------------------------

/// Result of a hybrid ancestor walk that uses `chain_tree` first and
/// falls back to `block_cache` when chain_tree is missing a link.
#[derive(Debug, Clone)]
pub struct HybridWalk {
    /// Hashes from start_hash (index 0) back to the terminating block.
    pub chain: Vec<[u8; 32]>,
    /// True if the walk terminated at a block with `prev_hash = None`
    /// (i.e. genesis child); false if it terminated at a missing parent
    /// or the start block was unknown.
    pub reached_origin: bool,
}

/// Result of a single pass of the Haskell-aligned chain selection.
#[derive(Debug, Clone)]
pub enum SelectionDecision {
    /// No peer has a chain strictly better than the adopted tip.
    NoBetterChain,
    /// A peer has a better tip but its chain doesn't connect to the
    /// adopted chain within the visibility window.
    OrphanCandidate { peer_id: PeerId, tip_block_no: u64 },
    /// A peer has a better tip and all blocks from the common ancestor
    /// to its tip are already validated — a fork switch can happen
    /// immediately.
    Switched {
        peer_id: PeerId,
        ancestor: [u8; 32],
        replay: Vec<[u8; 32]>,
        tip_block_no: u64,
    },
    /// A peer has a better tip but some replay blocks aren't fetched.
    WaitingForBlocks {
        peer_id: PeerId,
        ancestor: [u8; 32],
        anchor_point: Option<Point>,
        missing: Vec<Point>,
        tip_block_no: u64,
    },
}

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

/// Praos consensus state for one node.
///
/// Fields are `pub` so adapter code can read and selectively
/// manipulate them.  Treat them as state-machine internals: prefer the
/// public methods, which preserve invariants and emit the right
/// effects.
pub struct PraosState {
    pub node_id: String,
    pub security_param_k: u64,

    pub chain_tree: ChainTree,
    pub adopted_tip_hash: Option<[u8; 32]>,

    /// Points of blocks this node produced.
    pub self_produced: BTreeSet<Point>,
    /// All block bodies we possess.  Pruned beyond k.
    pub block_cache: BTreeMap<[u8; 32], CachedBlock>,
    /// Hashes of cached blocks that have passed validation.
    pub validated: BTreeSet<[u8; 32]>,

    /// Per-peer announced chains.  Drives chain selection.
    pub peer_chains: BTreeMap<PeerId, PeerChain>,
    /// Peers on cooldown after being classified as `OrphanCandidate`.
    pub orphan_cooldown: BTreeMap<PeerId, Instant>,
    /// Peers on cooldown after a `BlockFetch` request failed.  Excluded
    /// from chain selection until the timestamp passes — the fetch
    /// policy then has fresh information ("avoid this peer for a bit")
    /// and routes the next attempt elsewhere.
    pub block_fetch_cooldown: BTreeMap<PeerId, Instant>,

    /// Points currently being fetched (avoid duplicate requests).
    pub in_flight: BTreeMap<Point, Instant>,
    /// Gap-bridge rate-limit: `(adopted_tip_point, next_allowed)`.  The
    /// bridge re-fetches `[adopted_tip → best_tip]`; this stops it from
    /// re-issuing every retry tick while `best_tip` advances.  Cleared
    /// (allowed immediately) when the adopted tip changes.
    pub bridge_cooldown: Option<(Point, Instant)>,
    /// Hashes already submitted to the validator but not yet
    /// `Applied` / `ApplyFailed`.
    pub in_flight_validation: BTreeSet<[u8; 32]>,

    /// Hash the validator's queue will be at after every command we've
    /// already submitted has been processed.
    pub queued_validator_tip: Option<[u8; 32]>,
    /// Hash of the last block the validator has actually `Applied`.
    pub last_validated_tip: Option<[u8; 32]>,
    /// Wall-clock instant of the last successful validation.  Drives the
    /// once-per-minute "chain stuck" rollup WARN; `None` until the first
    /// block is validated so a freshly-booted node doesn't immediately
    /// complain about being stuck.
    pub last_validated_at: Option<Instant>,
    /// Throttle for the stuck-rollup WARN: the timestamp of the most
    /// recent emission.  Compared against [`STUCK_WARNING_INTERVAL`].
    pub last_stuck_warning_at: Option<Instant>,
    /// Per-peer throttle for the ChainSync ingress-time non-contiguous
    /// header WARN.  Compared against [`GAP_WARNING_INTERVAL`].
    pub last_gap_warning_at: BTreeMap<PeerId, Instant>,

    /// Slot at which this node first observed each header hash.
    /// Populated by [`PraosState::note_header_first_seen`] from any
    /// arrival path the I/O wrapper recognises as "header seen for the
    /// first time" (peer tip announcement, fetched body, self-produced).
    /// Used by [`PraosState::adopted_tip_header_arrival_slot`] for the
    /// CIP-0164 `LateRBHeader` voting predicate.  Pruned alongside
    /// `block_cache` on the k-prune path.
    pub header_first_seen: BTreeMap<[u8; 32], u64>,

    /// CIP-0164 RB-header equivocation tracker.  Per `(slot, issuer)`
    /// pair, the set of distinct RB header hashes observed.  The
    /// tracker is fed from every path that surfaces a parsed header
    /// (`on_block_received`, `register_self_produced`); insertions
    /// that grow a set past size 1 flag the slot in
    /// [`PraosState::equivocating_rb_slots`].
    pub header_hashes_by_slot_issuer: BTreeMap<(u64, Vec<u8>), BTreeSet<[u8; 32]>>,
    /// Slots at which RB-header equivocation has been detected.
    /// CIP-0164's "It has not detected any equivocating RB header for
    /// the same slot" voting condition consults this set via
    /// [`Self::is_equivocating_slot`].
    pub equivocating_rb_slots: BTreeSet<u64>,

    /// Strategy for picking peer(s) to fetch each block-range from.
    pub block_policy: Box<dyn BlockFetchPolicy + Send + Sync>,
    /// Live per-peer RTT lookup, consulted by `block_policy` at every
    /// fetch decision.
    pub rtt: Box<dyn PeerRtt + Send + Sync>,

    /// Pluggable behaviour; see [`crate::behaviour`].  Shared with the
    /// I/O wrapper as an `Arc<Mutex<Box<dyn _>>>` so out-of-band callers
    /// (e.g. per-peer outbound transforms) can lock the same behaviour
    /// instance.  Swapping the inner `Box` under the lock changes the
    /// live behaviour for every Arc holder.
    pub behaviour: Arc<Mutex<Box<dyn crate::behaviour::Behaviour>>>,
}

impl PraosState {
    /// Construct a new state with the default fetch policy
    /// ([`LowestRttFirst`]) and a zero-RTT [`UniformRtt`] oracle.  Test
    /// setups and adapters that don't care about peer ranking can use
    /// this; production wrappers should follow up with
    /// [`PraosState::set_fetch_policy`] / [`PraosState::set_rtt`].
    pub fn new(node_id: String, security_param_k: u64) -> Self {
        Self::with_fetch(
            node_id,
            security_param_k,
            Box::new(LowestRttFirst),
            Box::new(UniformRtt(Duration::ZERO)),
        )
    }

    /// Construct a new state with explicit fetch routing handles.
    pub fn with_fetch(
        node_id: String,
        security_param_k: u64,
        block_policy: Box<dyn BlockFetchPolicy + Send + Sync>,
        rtt: Box<dyn PeerRtt + Send + Sync>,
    ) -> Self {
        Self {
            node_id,
            security_param_k,
            chain_tree: ChainTree::new(),
            adopted_tip_hash: None,
            self_produced: BTreeSet::new(),
            block_cache: BTreeMap::new(),
            validated: BTreeSet::new(),
            peer_chains: BTreeMap::new(),
            orphan_cooldown: BTreeMap::new(),
            block_fetch_cooldown: BTreeMap::new(),
            in_flight: BTreeMap::new(),
            bridge_cooldown: None,
            in_flight_validation: BTreeSet::new(),
            queued_validator_tip: None,
            last_validated_tip: None,
            last_validated_at: None,
            last_stuck_warning_at: None,
            last_gap_warning_at: BTreeMap::new(),
            header_first_seen: BTreeMap::new(),
            header_hashes_by_slot_issuer: BTreeMap::new(),
            equivocating_rb_slots: BTreeSet::new(),
            block_policy,
            rtt,
            behaviour: Arc::new(Mutex::new(Box::new(crate::behaviour::HonestBehaviour))),
        }
    }

    /// Replace the behaviour.  Swaps the trait object under the mutex;
    /// other Arc holders observe the new behaviour from their next hook
    /// call.
    pub fn set_behaviour(&mut self, behaviour: Box<dyn crate::behaviour::Behaviour>) {
        *self.behaviour.lock().expect("behaviour mutex poisoned") = behaviour;
    }

    /// Short name of the current behaviour.
    pub fn behaviour_name(&self) -> &'static str {
        self.behaviour
            .lock()
            .expect("behaviour mutex poisoned")
            .name()
    }

    /// Lock the behaviour and call the hook with `(&mut dyn Behaviour,
    /// &PraosState)`.  The Arc clone breaks the borrow chain so the
    /// hook can see an immutable view of `self`.
    fn invoke_hook<F>(&mut self, hook: F) -> crate::behaviour::BehaviourOutcome<PraosEffect>
    where
        F: FnOnce(
            &mut dyn crate::behaviour::Behaviour,
            &PraosState,
        ) -> crate::behaviour::BehaviourOutcome<PraosEffect>,
    {
        let arc = self.behaviour.clone();
        let mut guard = arc.lock().expect("behaviour mutex poisoned");
        hook(&mut **guard, self)
    }

    /// Replace the block-fetch policy.
    pub fn set_fetch_policy(&mut self, policy: Box<dyn BlockFetchPolicy + Send + Sync>) {
        self.block_policy = policy;
    }

    /// Replace the per-peer RTT oracle.
    pub fn set_rtt(&mut self, rtt: Box<dyn PeerRtt + Send + Sync>) {
        self.rtt = rtt;
    }

    // -- Queries ------------------------------------------------------------

    /// Cap per-peer chain fragments at `2 * k` headers.
    pub fn peer_chain_cap(&self) -> usize {
        (self.security_param_k as usize).saturating_mul(2).max(64)
    }

    /// Snapshot the sizes of every internal collection plus rough byte
    /// estimates for the equivocation maps (suspect #2 in the per-node
    /// memory-leak audit).  Used by adapters to emit per-slot telemetry
    /// and by `log_state_sizes` for the periodic info line.
    pub fn state_sizes(&self) -> PraosStateSizes {
        let peer_chain_total: usize = self.peer_chains.values().map(|c| c.len()).sum();
        let peer_chain_max: usize = self
            .peer_chains
            .values()
            .map(|c| c.len())
            .max()
            .unwrap_or(0);
        let issuer_key_count = self.header_hashes_by_slot_issuer.len();
        let issuer_hashes_total: usize = self
            .header_hashes_by_slot_issuer
            .values()
            .map(|s| s.len())
            .sum();
        // Rough byte estimate: outer BTreeMap entry ~ 100 bytes (key tuple
        // + tree overhead, amortized); each inner BTreeSet<[u8;32]> entry
        // ~ 80 bytes (32-byte hash + tree overhead).
        let equivocation_bytes_estimate = issuer_key_count * 100
            + issuer_hashes_total * 80
            + self.equivocating_rb_slots.len() * 56;
        PraosStateSizes {
            chain_tree: self.chain_tree.len(),
            block_cache: self.block_cache.len(),
            validated: self.validated.len(),
            in_flight: self.in_flight.len(),
            in_flight_validation: self.in_flight_validation.len(),
            self_produced: self.self_produced.len(),
            peer_chains: self.peer_chains.len(),
            peer_chain_total,
            peer_chain_max,
            header_first_seen: self.header_first_seen.len(),
            header_hashes_by_slot_issuer: issuer_key_count,
            issuer_hashes_total,
            equivocating_rb_slots: self.equivocating_rb_slots.len(),
            orphan_cooldown: self.orphan_cooldown.len(),
            block_fetch_cooldown: self.block_fetch_cooldown.len(),
            equivocation_bytes_estimate,
        }
    }

    /// Emit an `info!` line summarising the sizes of every internal
    /// collection.  Used by adapters to monitor memory growth — if any
    /// collection grows without bound across consecutive lines, that's
    /// the leak.
    pub fn log_state_sizes(&self) {
        let s = self.state_sizes();
        info!(
            node_id = %self.node_id,
            chain_tree = s.chain_tree,
            block_cache = s.block_cache,
            validated = s.validated,
            in_flight = s.in_flight,
            in_flight_validation = s.in_flight_validation,
            self_produced = s.self_produced,
            peer_chains = s.peer_chains,
            peer_chain_total = s.peer_chain_total,
            peer_chain_max = s.peer_chain_max,
            header_first_seen = s.header_first_seen,
            header_hashes_by_slot_issuer = s.header_hashes_by_slot_issuer,
            issuer_hashes_total = s.issuer_hashes_total,
            equivocating_rb_slots = s.equivocating_rb_slots,
            orphan_cooldown = s.orphan_cooldown,
            block_fetch_cooldown = s.block_fetch_cooldown,
            equivocation_bytes_estimate = s.equivocation_bytes_estimate,
            "praos state sizes"
        );
    }

    /// Hash of the currently adopted tip, if any.
    pub fn tip_hash(&self) -> Option<[u8; 32]> {
        self.adopted_tip_hash
    }

    /// Block number to assign to the next self-produced block.
    pub fn next_block_number(&self) -> u64 {
        self.adopted_tip_hash
            .and_then(|h| self.chain_tree.block_number(&h))
            .map_or(1, |bn| bn + 1)
    }

    /// `(point, block_no)` of the adopted tip, if any.  Used by the I/O
    /// wrapper to construct a wire-format `Tip`.
    pub fn local_tip(&self) -> Option<(Point, u64)> {
        self.chain_tree
            .best_tip()
            .map(|(point, block_no)| (point.clone(), block_no))
    }

    /// Production slot of the adopted RB tip, if any.  Feeds
    /// [`crate::leios::ChainTipContext::tip_rb_slot`] for the chain-
    /// progress prune in [`crate::leios::LeiosState::on_slot`].
    pub fn adopted_tip_rb_slot(&self) -> Option<u64> {
        let hash = self.adopted_tip_hash?;
        self.chain_tree.point(&hash).and_then(|p| match p {
            Point::Specific { slot, .. } => Some(*slot),
            Point::Origin => None,
        })
    }

    /// Slot at which the adopted tip RB's header was first observed
    /// locally.  Falls back to the RB's own slot if the I/O wrapper
    /// never called [`PraosState::note_header_first_seen`] for this hash — that's a
    /// conservative best-case ("header can't have arrived before its
    /// own slot") and is what the CIP-0164 `LateRBHeader` voting
    /// predicate consults via the chain-tip context.
    pub fn adopted_tip_header_arrival_slot(&self) -> Option<u64> {
        let hash = self.adopted_tip_hash?;
        if let Some(slot) = self.header_first_seen.get(&hash) {
            return Some(*slot);
        }
        match self.chain_tree.point(&hash)? {
            Point::Specific { slot, .. } => Some(*slot),
            Point::Origin => None,
        }
    }

    /// EB hash announced by the adopted tip RB header, if any.  The
    /// I/O wrapper sets this when it parses a header into
    /// [`ParsedHeaderInfo`]; pre-Leios or opaque-header adoptions
    /// return `None`.
    pub fn adopted_tip_announced_eb(&self) -> Option<[u8; 32]> {
        self.block_cache
            .get(&self.adopted_tip_hash?)
            .and_then(|cb| cb.announced_eb_hash)
    }

    /// If the block at `point` carries a CIP-0164 cert for its
    /// parent's announced EB, return the parent RB's slot and the
    /// announced EB hash.  Used by the I/O wrapper to feed
    /// [`crate::leios::LeiosState::on_chain_endorsement`] on every
    /// successful block apply.
    pub fn parent_announced_eb_for_cert(&self, point: &Point) -> Option<(u64, [u8; 32])> {
        let hash = match point {
            Point::Specific { hash, .. } => *hash,
            Point::Origin => return None,
        };
        let cb = self.block_cache.get(&hash)?;
        if !cb.certified_eb {
            return None;
        }
        let parent_hash = cb.prev_hash?;
        let parent = self.block_cache.get(&parent_hash)?;
        let parent_eb_hash = parent.announced_eb_hash?;
        let parent_slot = match &parent.point {
            Point::Specific { slot, .. } => *slot,
            Point::Origin => return None,
        };
        Some((parent_slot, parent_eb_hash))
    }

    /// Record that this node first observed `header_hash` at slot
    /// `current_slot`.  Idempotent — only the first call for a given
    /// hash takes effect, so callers can invoke it from any path that
    /// surfaces a header (peer tip announcement, fetched body, self-
    /// produced) without coordinating among them.
    pub fn note_header_first_seen(&mut self, header_hash: [u8; 32], current_slot: u64) {
        self.header_first_seen
            .entry(header_hash)
            .or_insert(current_slot);
    }

    /// Record an observed RB header for equivocation detection.
    /// Called from every path that surfaces a parsed header
    /// (`on_block_received`, `register_self_produced`).  If `issuer`
    /// is empty, detection is skipped for this header (allows
    /// pre-issuer callers to no-op).  If a second distinct hash
    /// arrives for the same `(slot, issuer)`, the slot is added to
    /// [`Self::equivocating_rb_slots`] and CIP-0164 voters will
    /// abstain from voting on any EB associated with that slot.
    fn note_header_for_equivocation(&mut self, slot: u64, issuer: &[u8], header_hash: [u8; 32]) {
        if issuer.is_empty() {
            return;
        }
        let key = (slot, issuer.to_vec());
        let set = self.header_hashes_by_slot_issuer.entry(key).or_default();
        let was_new = set.insert(header_hash);
        if set.len() > 1 && was_new {
            self.equivocating_rb_slots.insert(slot);
            info!(
                node_id = %self.node_id,
                slot,
                hashes = set.len(),
                "RB-header equivocation detected"
            );
        }
    }

    /// True iff RB-header equivocation has been detected at `slot`.
    /// Surfaced to the Leios voting predicate through
    /// [`crate::leios::ChainTipContext::equivocating_slots`].
    pub fn is_equivocating_slot(&self, slot: u64) -> bool {
        self.equivocating_rb_slots.contains(&slot)
    }

    /// Snapshot the recent chain tree for UI display.
    ///
    /// `eb_manifest_count` resolves an announced-EB hash to the length
    /// of its tx-hash manifest (typically `LeiosState::eb_tx_hashes`
    /// lookup at the wrapper boundary). Returns `None` when the manifest
    /// hasn't been cached yet.
    pub fn chain_tree_snapshot(
        &self,
        eb_manifest_count: impl Fn(&[u8; 32]) -> Option<u32>,
    ) -> (Vec<ChainTreeEntry>, Option<u64>, Option<String>) {
        match self.adopted_tip_hash {
            Some(hash) => {
                let block_no = self.chain_tree.block_number(&hash);
                let entries = self
                    .chain_tree
                    .snapshot(hash, 10, block_no, eb_manifest_count);
                let tip_hash = Some(format!("{:02x}{:02x}", hash[30], hash[31]));
                (entries, block_no, tip_hash)
            }
            None => (Vec::new(), None, None),
        }
    }

    /// Stash the tx-count of an EB once its manifest is known locally.
    /// The I/O wrapper calls this from both the self-produce path and
    /// the LeiosFetch receive path.  The count is cached on the
    /// chain-tree node that announced the EB, so
    /// [`Self::chain_tree_snapshot`] can surface it after the wrapper's
    /// short-lived manifest cache has aged out.
    pub fn record_announced_eb_tx_count(&mut self, eb_hash: &[u8; 32], count: u32) {
        self.chain_tree.record_announced_eb_tx_count(eb_hash, count);
    }

    // -- Peer-event mutations (no effects) ----------------------------------

    /// Append a peer's announced header to its candidate chain.  The
    /// caller has already extracted the header's `block_no`, `slot`,
    /// `prev_hash`, and the announced `tip` from the wire types.
    #[allow(clippy::too_many_arguments)]
    pub fn record_peer_tip(
        &mut self,
        peer_id: PeerId,
        tip_point: Point,
        tip_block_no: u64,
        header_block_no: u64,
        header_hash: [u8; 32],
        header_slot: u64,
        header_prev_hash: Option<[u8; 32]>,
    ) {
        // The announced header may be an ancestor of `tip` while a peer
        // catches up.  Use whichever pair matches.
        let (hash, point) = if header_block_no == tip_block_no {
            match &tip_point {
                Point::Specific { hash, .. } => (*hash, tip_point.clone()),
                _ => return,
            }
        } else {
            (
                header_hash,
                Point::Specific {
                    hash: header_hash,
                    slot: header_slot,
                },
            )
        };
        let entry = PeerChainEntry {
            hash,
            point,
            block_no: header_block_no,
            prev_hash: header_prev_hash,
        };
        let cap = self.peer_chain_cap();
        let chain = self
            .peer_chains
            .entry(peer_id)
            .or_insert_with(|| PeerChain::new(cap));

        // Detect non-contiguous ChainSync forwarding: the just-arrived
        // header should link to the previously-announced one's hash via
        // `prev_hash`.  When it doesn't, the upstream skipped one or more
        // blocks on this branch.  PeerChain doesn't enforce contiguity
        // (sliding-window cap means some divergence is expected at the
        // anchor edge), so we check explicitly here and only fire when
        // the previous entry is still in the window — that rules out
        // anchor-edge false positives.
        let gap_after_hash =
            chain
                .iter()
                .next_back()
                .and_then(|prev| match (entry.prev_hash, prev.hash) {
                    (Some(p), h) if p != h => Some((prev.hash, prev.block_no, prev.point.clone())),
                    _ => None,
                });

        chain.append(entry);

        if let Some((prev_hash, prev_block_no, prev_point)) = gap_after_hash {
            let now = Instant::now();
            let throttled = matches!(
                self.last_gap_warning_at.get(&peer_id),
                Some(last) if now.saturating_duration_since(*last) < GAP_WARNING_INTERVAL,
            );
            if !throttled {
                warn!(
                    node_id = %self.node_id,
                    %peer_id,
                    prev_block_no,
                    %prev_point,
                    prev_hash = format!(
                        "{:02x}{:02x}{:02x}{:02x}",
                        prev_hash[0], prev_hash[1], prev_hash[2], prev_hash[3]
                    ),
                    new_block_no = header_block_no,
                    new_prev_hash_expected = format!(
                        "{:02x}{:02x}{:02x}{:02x}",
                        prev_hash[0], prev_hash[1], prev_hash[2], prev_hash[3]
                    ),
                    new_prev_hash_actual = header_prev_hash.map(|h| format!(
                        "{:02x}{:02x}{:02x}{:02x}",
                        h[0], h[1], h[2], h[3]
                    )).unwrap_or_else(|| "none".to_string()),
                    gap_block_count = header_block_no.saturating_sub(prev_block_no).saturating_sub(1),
                    "ChainSync forwarded a non-contiguous header: upstream skipped one or more blocks between the last announced tip and this one"
                );
                self.last_gap_warning_at.insert(peer_id, now);
            }
        }
    }

    /// Store the ChainSync intersection as the peer chain's anchor.
    pub fn record_peer_intersection(&mut self, peer_id: PeerId, point: Point) {
        let cap = self.peer_chain_cap();
        self.peer_chains
            .entry(peer_id)
            .or_insert_with(|| PeerChain::new(cap))
            .set_anchor(point);
    }

    /// Truncate a peer's candidate chain on a rollback.
    pub fn record_peer_rollback(&mut self, peer_id: PeerId, point: &Point) {
        if let Some(chain) = self.peer_chains.get_mut(&peer_id) {
            chain.rollback_to(point);
        }
    }

    /// Drop a peer's candidate chain on disconnect.  Also clears any
    /// orphan cooldown entry for that peer.
    pub fn record_peer_disconnected(&mut self, peer_id: PeerId) {
        self.peer_chains.remove(&peer_id);
        self.orphan_cooldown.remove(&peer_id);
        self.last_gap_warning_at.remove(&peer_id);
    }

    // -- High-level event handlers (effect-emitting) ------------------------

    /// A peer announced a new tip.  Records it and runs chain selection.
    #[allow(clippy::too_many_arguments)]
    pub fn on_tip_advanced(
        &mut self,
        peer_id: PeerId,
        tip_point: Point,
        tip_block_no: u64,
        header_block_no: u64,
        header_hash: [u8; 32],
        header_slot: u64,
        header_prev_hash: Option<[u8; 32]>,
        header_issuer: &[u8],
        now: Instant,
    ) -> Vec<PraosEffect> {
        use crate::behaviour::BehaviourOutcome;
        let tip_clone = tip_point.clone();
        let appended: Vec<PraosEffect> =
            match self.invoke_hook(|b, s| b.on_tip_advanced(s, peer_id, &tip_clone)) {
                BehaviourOutcome::Continue => Vec::new(),
                BehaviourOutcome::Replace(effects) => return effects,
                BehaviourOutcome::Append(extra) => extra,
            };
        // CIP-0164 RB-header equivocation: detect as soon as a second
        // distinct header hash arrives at the same `(slot, issuer)` via
        // the ChainSync announce path, without waiting for the body
        // fetch.  Without this, an adversary that advertises divergent
        // headers to disjoint peer subsets can prevent detection for
        // any peer that follows only one variant's body.
        self.note_header_for_equivocation(header_slot, header_issuer, header_hash);
        self.record_peer_tip(
            peer_id,
            tip_point,
            tip_block_no,
            header_block_no,
            header_hash,
            header_slot,
            header_prev_hash,
        );
        let mut fx = Vec::new();
        self.evaluate_and_fetch_internal(now, &mut fx);
        fx.extend(appended);
        fx
    }

    /// A fetched block arrived.  Caches it and tries a fork switch
    /// targeting this specific block.  `parsed_header` is `Some` when
    /// the wrapper successfully parsed the header into block-no /
    /// slot / prev-hash; `None` for opaque headers.
    #[allow(clippy::too_many_arguments)]
    pub fn on_block_received(
        &mut self,
        point: Point,
        header_bytes: Vec<u8>,
        body_bytes: Vec<u8>,
        parsed_header: Option<ParsedHeaderInfo>,
        tx_count: u32,
    ) -> Vec<PraosEffect> {
        use crate::behaviour::BehaviourOutcome;
        let appended: Vec<PraosEffect> =
            match self.invoke_hook(|b, s| b.on_block_received(s, &point)) {
                BehaviourOutcome::Continue => Vec::new(),
                BehaviourOutcome::Replace(effects) => return effects,
                BehaviourOutcome::Append(extra) => extra,
            };
        let mut fx = Vec::new();
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => {
                fx.extend(appended);
                return fx;
            }
        };
        // Dedup.
        if self.block_cache.contains_key(&hash)
            || self.validated.contains(&hash)
            || self.in_flight_validation.contains(&hash)
        {
            fx.extend(appended);
            return fx;
        }
        let header_was_parsed = parsed_header.is_some();
        let (block_no, slot, prev_hash, announced_eb_hash, certified_eb, issuer) =
            match parsed_header {
                Some(info) => (
                    info.block_number,
                    info.slot,
                    info.prev_hash,
                    info.announced_eb_hash,
                    info.certified_eb,
                    info.issuer,
                ),
                None => (
                    self.chain_tree.block_number(&hash).unwrap_or(0),
                    match &point {
                        Point::Specific { slot, .. } => *slot,
                        _ => 0,
                    },
                    self.chain_tree.prev_hash(&hash),
                    None,
                    false,
                    Vec::new(),
                ),
            };
        // CIP-0164 RB-header equivocation tracking — must run on
        // every distinct header observed (before any dedup that
        // would short-circuit the path).  Honored across both
        // peer-received and self-produced headers; a node that
        // self-produces two headers at the same slot equivocates too.
        self.note_header_for_equivocation(slot, &issuer, hash);
        // Insert into chain_tree only when we have a real block_no
        // (parsed header) or, for opaque headers, when fallback metadata
        // is non-default.  Inserting block_no=0 confuses pruning.
        if header_was_parsed || block_no > 0 {
            self.chain_tree.insert(
                hash,
                point.clone(),
                block_no,
                slot,
                prev_hash,
                tx_count,
                announced_eb_hash,
                certified_eb,
            );
        }
        self.block_cache.insert(
            hash,
            CachedBlock {
                point: point.clone(),
                block_no,
                prev_hash,
                header: header_bytes,
                body: body_bytes,
                announced_eb_hash,
                certified_eb,
            },
        );
        info!(
            node_id = %self.node_id,
            %point,
            block_no,
            "block received and cached"
        );
        self.try_switch_and_execute_internal(hash, &mut fx);
        fx.extend(appended);
        fx
    }

    /// A `BlockFetch` failed for the requested range.  Drop the
    /// in-flight markers, put the responsible peer on cooldown, and
    /// re-run chain selection — which now has fresh information ("this
    /// peer just failed for this range") and lets the fetch policy
    /// pick a different candidate.  Without the cooldown, `select_chain`
    /// reaches the same `WaitingForBlocks { peer_id }` decision and
    /// re-fetches the same range from the same peer in microseconds.
    pub fn on_block_fetch_failed(
        &mut self,
        peer_id: PeerId,
        from: &Point,
        to: &Point,
        now: Instant,
    ) -> Vec<PraosEffect> {
        // Clear the whole failed range, not just its endpoints: blocks are
        // now tracked in flight individually, so drop every in-flight marker
        // whose slot falls within [from, to] so re-selection can refetch the
        // entire range from a different peer.
        let slot_of = |p: &Point| match p {
            Point::Specific { slot, .. } => Some(*slot),
            Point::Origin => None,
        };
        if let (Some(from_slot), Some(to_slot)) = (slot_of(from), slot_of(to)) {
            self.in_flight.retain(|p, _| match slot_of(p) {
                Some(s) => s < from_slot || s > to_slot,
                None => true,
            });
        } else {
            self.in_flight.remove(from);
            self.in_flight.remove(to);
        }
        self.block_fetch_cooldown
            .insert(peer_id, now + BLOCK_FETCH_COOLDOWN);
        debug!(
            node_id = %self.node_id,
            %peer_id, %from, %to,
            "block fetch failed; cooling peer and re-evaluating"
        );
        let mut fx = Vec::new();
        self.evaluate_and_fetch_internal(now, &mut fx);
        fx
    }

    /// A peer rolled its chain back; truncate its fragment and re-run
    /// chain selection.
    pub fn on_peer_rolled_back(
        &mut self,
        peer_id: PeerId,
        point: &Point,
        now: Instant,
    ) -> Vec<PraosEffect> {
        self.record_peer_rollback(peer_id, point);
        info!(
            node_id = %self.node_id,
            %peer_id,
            to = %point,
            "peer chain rolled back"
        );
        let mut fx = Vec::new();
        self.evaluate_and_fetch_internal(now, &mut fx);
        fx
    }

    /// A peer disconnected; drop its fragment and re-run selection in
    /// case its absence frees up a different peer.
    pub fn on_peer_disconnected(&mut self, peer_id: PeerId, now: Instant) -> Vec<PraosEffect> {
        use crate::behaviour::BehaviourOutcome;
        let appended: Vec<PraosEffect> =
            match self.invoke_hook(|b, s| b.on_peer_disconnected(s, peer_id)) {
                BehaviourOutcome::Continue => Vec::new(),
                BehaviourOutcome::Replace(effects) => return effects,
                BehaviourOutcome::Append(extra) => extra,
            };
        self.record_peer_disconnected(peer_id);
        let mut fx = Vec::new();
        self.evaluate_and_fetch_internal(now, &mut fx);
        fx.extend(appended);
        fx
    }

    // -- Self-production ----------------------------------------------------

    /// Register a block we produced ourselves.  Caches it, hands it to
    /// the validator, and runs a fork-switch attempt.
    #[allow(clippy::too_many_arguments)]
    pub fn register_self_produced(
        &mut self,
        point: Point,
        header_bytes: Vec<u8>,
        body_bytes: Vec<u8>,
        parsed_header: Option<ParsedHeaderInfo>,
        tx_count: u32,
    ) -> Vec<PraosEffect> {
        let mut fx = Vec::new();
        self.self_produced.insert(point.clone());
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return fx,
        };
        match parsed_header {
            Some(info) => {
                // CIP-0164 equivocation tracking — a producer that
                // self-produces multiple headers at the same slot
                // equivocates against itself.  Tracker is honest
                // about that, so honest voters abstain even on
                // their own conflicting EBs.
                self.note_header_for_equivocation(info.slot, &info.issuer, hash);
                self.chain_tree.insert(
                    hash,
                    point.clone(),
                    info.block_number,
                    info.slot,
                    info.prev_hash,
                    tx_count,
                    info.announced_eb_hash,
                    info.certified_eb,
                );
                self.block_cache.entry(hash).or_insert(CachedBlock {
                    point: point.clone(),
                    block_no: info.block_number,
                    prev_hash: info.prev_hash,
                    header: header_bytes,
                    body: body_bytes.clone(),
                    announced_eb_hash: info.announced_eb_hash,
                    certified_eb: info.certified_eb,
                });
                self.submit_for_validation_internal(point, body_bytes, info.prev_hash, &mut fx);
                self.try_switch_and_execute_internal(hash, &mut fx);
            }
            None => {
                // Opaque header — submit body to validator, skip
                // chain_tree insertion.
                self.submit_for_validation_internal(point, body_bytes, None, &mut fx);
            }
        }
        fx
    }

    // -- Validation outcomes ------------------------------------------------

    /// Validator reported a successful Apply.  Publish the block to the
    /// chain store, update last-validated tip, prune below k, and re-
    /// run chain selection.
    pub fn on_block_applied(&mut self, point: Point, now: Instant) -> Vec<PraosEffect> {
        let mut fx = Vec::new();
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return fx,
        };
        self.in_flight.remove(&point);
        self.in_flight_validation.remove(&hash);
        let inject = match self.block_cache.get(&hash) {
            Some(cb) => PraosEffect::InjectBlock {
                point: cb.point.clone(),
                header: cb.header.clone(),
                body: cb.body.clone(),
                block_no: cb.block_no,
            },
            None => {
                warn!(
                    node_id = %self.node_id,
                    %point,
                    "applied outcome for block not in cache — ignoring"
                );
                return fx;
            }
        };
        self.validated.insert(hash);
        self.last_validated_tip = Some(hash);
        self.last_validated_at = Some(now);
        info!(
            node_id = %self.node_id,
            %point,
            "block validated, publishing to chain store"
        );
        fx.push(inject);
        // Prune old blocks beyond k.
        if let Some(adopted) = self.adopted_tip_hash {
            if let Some(bn) = self.chain_tree.block_number(&adopted) {
                if bn > self.security_param_k {
                    let min = bn - self.security_param_k;
                    self.chain_tree.prune_below(min);
                    self.block_cache.retain(|_, cb| cb.block_no >= min);
                    self.validated.retain(|h| self.block_cache.contains_key(h));
                    self.header_first_seen
                        .retain(|h, _| self.block_cache.contains_key(h));
                }
            }
        }
        // Try switching to chain_tree's best tip, then evaluate peers.
        if let Some(best) = self.chain_tree.best_tip_hash() {
            self.try_switch_and_execute_internal(best, &mut fx);
        }
        self.evaluate_and_fetch_internal(now, &mut fx);
        fx
    }

    /// Validator reported an Apply failure.  Rewind the queue
    /// projection so the next submission realigns with the ledger.
    pub fn on_block_apply_failed(&mut self, point: Point, error: String) {
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        self.in_flight.remove(&point);
        self.in_flight_validation.remove(&hash);
        warn!(
            node_id = %self.node_id,
            %point,
            %error,
            "ledger apply failed; rewinding to last validated tip"
        );
        self.queued_validator_tip = self.last_validated_tip;
        self.adopted_tip_hash = self.last_validated_tip;
        self.validated.remove(&hash);
    }

    /// Validator reported a successful Rollback.  Mirror it in the
    /// chain store.
    pub fn on_block_rolled_back(&mut self, target: Point) -> Vec<PraosEffect> {
        let mut fx = Vec::new();
        if target == Point::Origin {
            self.last_validated_tip = None;
            info!(
                node_id = %self.node_id,
                "ledger rolled back to Origin, clearing chain store"
            );
            fx.push(PraosEffect::InjectRollback {
                target: Point::Origin,
            });
            return fx;
        }
        let hash = match &target {
            Point::Specific { hash, .. } => *hash,
            _ => return fx,
        };
        self.last_validated_tip = Some(hash);
        info!(
            node_id = %self.node_id,
            %target,
            "ledger rolled back, rolling chain store"
        );
        fx.push(PraosEffect::InjectRollback { target });
        fx
    }

    /// Deliberately roll the *own* adopted chain back by `depth` blocks
    /// and re-anchor at that ancestor, abandoning the suffix, so the next
    /// block produced forks from there.  Emits `InjectRollback` so the
    /// served chain store mirrors it — downstream followers then see a
    /// `RollBackward(depth)` + `RollForward(fork)`.
    ///
    /// This is a deliberate self-reorg trigger (the `DeepReorg`
    /// behaviour); it is *not* part of honest consensus.  No-op if there
    /// is no adopted tip or the chain is shorter than `depth`.
    pub fn force_rollback(&mut self, depth: u64) -> Vec<PraosEffect> {
        let mut fx = Vec::new();
        if depth == 0 {
            return fx;
        }
        let tip = match self.adopted_tip_hash {
            Some(h) => h,
            None => return fx,
        };
        // ancestors() yields [tip, parent, grandparent, …]; index `depth`
        // is the block `depth` steps back.
        let ancestors = self.chain_tree.ancestors(tip);
        let target_hash = match ancestors.get(depth as usize) {
            Some(h) => *h,
            None => return fx, // chain too short to roll back this far
        };
        let target = match self.chain_tree.point(&target_hash) {
            Some(p) => p.clone(),
            None => return fx,
        };
        let target_bn = self.chain_tree.block_number(&target_hash).unwrap_or(0);

        // Re-anchor every chain-state pointer at the target.
        self.adopted_tip_hash = Some(target_hash);
        self.last_validated_tip = Some(target_hash);
        self.queued_validator_tip = Some(target_hash);
        // Drop the abandoned suffix so it can't be re-selected as best tip.
        self.chain_tree.remove_above(target_bn);
        // Evict the suffix from the cache too.  The dedup at the top of
        // `on_block_received` short-circuits when a hash is already in
        // `block_cache` / `validated` / `in_flight_validation`, so a peer
        // re-offering an abandoned block after the reorg would be silently
        // dropped — `chain_tree` would never re-acquire it and the node
        // would be pinned on its dead fork.  Mirror the k-prune retention
        // pattern in `on_block_applied`, opposite direction.
        self.block_cache.retain(|_, cb| cb.block_no <= target_bn);
        self.validated.retain(|h| self.block_cache.contains_key(h));
        self.in_flight_validation
            .retain(|h| self.block_cache.contains_key(h));
        self.header_first_seen
            .retain(|h, _| self.block_cache.contains_key(h));

        info!(
            node_id = %self.node_id,
            %target,
            depth,
            "force rollback: self-reorg, abandoning chain suffix"
        );
        fx.push(PraosEffect::InjectRollback { target });
        fx
    }

    // -- Periodic retry -----------------------------------------------------

    /// Periodic slot-driven retry: evict stale in-flight fetches and
    /// re-run chain selection.  Bridges chain_tree gaps when needed.
    pub fn retry_select_chain(&mut self, now: Instant) -> Vec<PraosEffect> {
        let mut fx = Vec::new();
        let before = self.in_flight.len();
        self.evict_stale_in_flight(now);
        let evicted = before - self.in_flight.len();

        if let Some(best) = self.chain_tree.best_tip_hash() {
            self.try_switch_and_execute_internal(best, &mut fx);
        }
        if evicted > 0 || !self.in_flight.is_empty() {
            self.evaluate_and_fetch_internal(now, &mut fx);
        }
        // Bridge a chain_tree gap between best_tip and adopted, if any.
        if let Some(best) = self.chain_tree.best_tip_hash() {
            if let Err(Some(gap_point)) = self.try_switch_to(best) {
                // Only bridge when we have a real lower-bound block: a
                // range anchored at Origin is rejected (and reset) by a
                // standard Cardano server, so we cannot bridge a gap
                // with no adopted tip to anchor against.
                let from = self
                    .adopted_tip_hash
                    .and_then(|h| self.chain_tree.point(&h).cloned());
                let from_slot = match from.as_ref() {
                    Some(Point::Specific { slot, .. }) => *slot,
                    _ => 0,
                };
                let to_slot = match &gap_point {
                    Point::Specific { slot, .. } => *slot,
                    _ => 0,
                };
                if let Some(from) = from {
                    // Rate-limit the bridge: skip if we recently bridged from
                    // this same adopted tip.  An advancing best_tip changes
                    // `gap_point` every tick and defeats the in-flight dedup,
                    // so without this the whole range re-fetches continuously.
                    let bridge_cooling = matches!(
                        &self.bridge_cooldown,
                        Some((cooled_from, until)) if *cooled_from == from && now < *until
                    );
                    if to_slot > from_slot
                        && !self.in_flight.contains_key(&gap_point)
                        && !bridge_cooling
                    {
                        let peers = self.choose_block_fetch_peers(&gap_point, None);
                        info!(
                            node_id = %self.node_id,
                            %from,
                            to = %gap_point,
                            peer_count = peers.len(),
                            "retry: fetching gap to bridge chain_tree"
                        );
                        self.in_flight.insert(gap_point.clone(), now);
                        self.bridge_cooldown = Some((from.clone(), now + BRIDGE_COOLDOWN));
                        fx.push(PraosEffect::FetchBlockRange {
                            from,
                            to: gap_point,
                            peers,
                        });
                    }
                }
            }
        }
        self.maybe_emit_stuck_warning(now);
        fx
    }

    /// Synthesised once-per-minute WARN that surfaces a wedged-chain
    /// diagnosis without forcing an operator to grep across the per-event
    /// INFO traffic.  Fires when:
    ///
    /// - we've validated at least one block (otherwise we're still
    ///   booting, not stuck),
    /// - validation has been frozen for [`STUCK_THRESHOLD`] or longer,
    /// - the throttle ([`STUCK_WARNING_INTERVAL`]) has elapsed since the
    ///   last emission, and
    /// - some peer announces a strictly-better tip than the one we've
    ///   adopted (otherwise there's nothing to be stuck on).
    ///
    /// The diagnostic counts how many entries in that peer's announced
    /// replay carry a `prev_hash` we don't have locally (neither in
    /// `chain_tree` nor in `block_cache`).  A nonzero count means the
    /// peer's chain has parents we never received — typically because
    /// ChainSync skipped their headers and BlockFetch range requests
    /// don't include them either.  In a healthy interop that count is
    /// zero; a steady nonzero count points the operator at an upstream
    /// chain inconsistency rather than at a local consensus bug.
    fn maybe_emit_stuck_warning(&mut self, now: Instant) {
        let last_validated_at = match self.last_validated_at {
            Some(t) => t,
            None => return,
        };
        let stuck_for = now.saturating_duration_since(last_validated_at);
        if stuck_for < STUCK_THRESHOLD {
            return;
        }
        if let Some(last) = self.last_stuck_warning_at {
            if now.saturating_duration_since(last) < STUCK_WARNING_INTERVAL {
                return;
            }
        }
        let our_block_no = self
            .adopted_tip_hash
            .and_then(|h| self.chain_tree.block_number(&h))
            .unwrap_or(0);
        // Pick the peer with the highest announced tip strictly above
        // ours.  Ties broken by PeerId order so the choice is stable
        // across calls; the warning is informational, not load-bearing.
        let best = self
            .peer_chains
            .iter()
            .filter_map(|(pid, chain)| chain.iter().next_back().map(|e| (*pid, e.block_no, chain)))
            .filter(|(_, bn, _)| *bn > our_block_no)
            .max_by_key(|(pid, bn, _)| (*bn, *pid));
        let (peer_id, peer_tip_block_no, peer_chain) = match best {
            Some(b) => b,
            None => return,
        };
        // "Unreachable" means we have no record of the parent at all,
        // anywhere in our local view of the network's chain.  Check the
        // whole `chain_tree` (every fork we've heard of, not just our
        // adopted ancestry) plus `block_cache` (fetched bodies not yet in
        // the tree).  Restricting to adopted-tip ancestors here would
        // false-positive whenever the peer's chain forks off into a
        // branch we hold but haven't adopted.
        let unreachable_parents = peer_chain
            .iter()
            .filter(|e| match e.prev_hash {
                Some(p) => {
                    self.chain_tree.block_number(&p).is_none()
                        && !self.block_cache.contains_key(&p)
                }
                None => false,
            })
            .count();
        warn!(
            node_id = %self.node_id,
            stuck_secs = stuck_for.as_secs(),
            adopted_tip_block_no = our_block_no,
            %peer_id,
            peer_tip_block_no,
            unreachable_parent_hashes = unreachable_parents,
            peer_chain_len = peer_chain.iter().count(),
            "chain stuck: best peer offers a strictly-better tip but its replay has parent hashes we never received — likely upstream chain inconsistency (gappy ChainSync forwarding)"
        );
        self.last_stuck_warning_at = Some(now);
    }

    // -- Pure algorithm queries (also used by tests) ------------------------

    /// Walk backward from `start_hash` following `prev_hash` links,
    /// using `chain_tree` first and falling back to `block_cache` when
    /// a block is cached but not yet in chain_tree.
    pub fn walk_ancestors_hybrid(&self, start_hash: [u8; 32]) -> HybridWalk {
        let mut chain = vec![start_hash];
        let mut current = start_hash;
        let reached_origin;
        loop {
            let parent_opt = if self.chain_tree.block_number(&current).is_some() {
                self.chain_tree.prev_hash(&current)
            } else if let Some(cached) = self.block_cache.get(&current) {
                cached.prev_hash
            } else {
                reached_origin = false;
                break;
            };
            match parent_opt {
                None => {
                    reached_origin = true;
                    break;
                }
                Some(parent) => {
                    let in_tree = self.chain_tree.block_number(&parent).is_some();
                    let in_cache = self.block_cache.contains_key(&parent);
                    if !in_tree && !in_cache {
                        reached_origin = false;
                        break;
                    }
                    chain.push(parent);
                    current = parent;
                }
            }
        }
        HybridWalk {
            chain,
            reached_origin,
        }
    }

    /// One pass of Haskell-aligned chain selection.  Pure: does not
    /// mutate state.  Tests call this directly to assert classification.
    pub fn select_chain_once(&self, skip: &HashSet<PeerId>) -> SelectionDecision {
        let (adopted_hash, adopted_bn) = match self.adopted_tip_hash {
            Some(h) => (h, self.chain_tree.block_number(&h).unwrap_or(0)),
            None => ([0u8; 32], 0),
        };
        let best = self
            .peer_chains
            .iter()
            .filter(|(peer_id, _)| !skip.contains(peer_id))
            .filter_map(|(peer_id, chain)| {
                let tip = chain.tip()?;
                if self.adopted_tip_hash.is_none()
                    || is_better_tip(tip.block_no, &tip.hash, adopted_bn, &adopted_hash)
                {
                    Some((*peer_id, chain, tip.clone()))
                } else {
                    None
                }
            })
            .max_by(|a, b| {
                a.2.block_no
                    .cmp(&b.2.block_no)
                    .then_with(|| b.2.hash.cmp(&a.2.hash))
            });

        let (peer_id, candidate, candidate_tip) = match best {
            Some(b) => b,
            None => return SelectionDecision::NoBetterChain,
        };

        let adopted_ancestors: HashSet<[u8; 32]> = self
            .adopted_tip_hash
            .map(|h| self.chain_tree.ancestors(h).into_iter().collect())
            .unwrap_or_default();

        let mut replay_rev: Vec<&PeerChainEntry> = Vec::new();
        let mut ancestor: Option<[u8; 32]> = None;
        for entry in candidate.iter().rev() {
            if adopted_ancestors.contains(&entry.hash) {
                ancestor = Some(entry.hash);
                break;
            }
            replay_rev.push(entry);
        }
        if ancestor.is_none() {
            if let Some(oldest) = candidate.iter().next() {
                match oldest.prev_hash {
                    None => {
                        // Candidate's oldest entry claims genesis as its
                        // parent.  Genesis is a universal common ancestor —
                        // every valid chain descends from it — so accept it
                        // here regardless of whether we have an adopted tip.
                        // Without this, a fork that diverges all the way
                        // back at block 1 produces a permanent
                        // OrphanCandidate verdict and the two sides never
                        // reconcile, even though `is_better_tip` would
                        // otherwise have picked a winner.
                        ancestor = Some([0u8; 32]);
                    }
                    Some(parent) => {
                        // Two paths to accept the parent as ancestor:
                        // either it's already in the adopted chain's
                        // ancestry, or we have no adopted chain (fresh
                        // node) so any parent is acceptable.
                        if adopted_ancestors.contains(&parent) || self.adopted_tip_hash.is_none() {
                            ancestor = Some(parent);
                        }
                    }
                }
            }
        }
        if ancestor.is_none() {
            if let Some(anchor) = candidate.anchor() {
                if anchor.hash == [0u8; 32] && self.adopted_tip_hash.is_none() {
                    ancestor = Some([0u8; 32]);
                } else if adopted_ancestors.contains(&anchor.hash) {
                    ancestor = Some(anchor.hash);
                }
            }
        }
        // Final fallback: trust the ChainSync intersection anchor as the
        // common ancestor even when it isn't in `adopted_ancestors`.  This
        // is the multi-peer reconnect-handover case: after reconnecting to
        // a peer on a divergent fork, our per-peer fragment is too short to
        // reach the fork point and `adopted_ancestors` may be truncated by
        // pruning — but `find_intersection` already probed back to genesis,
        // so its anchor is authoritative.  Bound the switch by k (Praos
        // finality): a reorg deeper than the security parameter would roll
        // back settled blocks, so it is refused (the peer is left
        // unresolved → OrphanCandidate → cooldown, no spin).
        //
        // Restricted to a *real block we hold* (not Origin): a switch that
        // shares only genesis needs a full re-sync from block 1, which the
        // range-fetch path can't anchor at Origin — that is out of scope
        // here and not the round-robin-backend case (those share real
        // history at the fork point).
        if ancestor.is_none() {
            if let Some(anchor) = candidate.anchor() {
                if anchor.hash != [0u8; 32] {
                    if let Some(anchor_bn) = self.chain_tree.block_number(&anchor.hash) {
                        let reorg_depth = adopted_bn.saturating_sub(anchor_bn);
                        if reorg_depth <= self.security_param_k {
                            info!(
                                node_id = %self.node_id,
                                %peer_id,
                                reorg_depth,
                                "select_chain: trusting intersection anchor as common ancestor (reorg within k)"
                            );
                            ancestor = Some(anchor.hash);
                        } else {
                            info!(
                                node_id = %self.node_id,
                                %peer_id,
                                reorg_depth,
                                k = self.security_param_k,
                                "select_chain: refusing reorg deeper than k (settled blocks); skipping peer"
                            );
                        }
                    }
                }
            }
        }
        let ancestor = match ancestor {
            Some(a) => a,
            None => {
                let hex_tail = |h: &[u8; 32]| format!("{:02x}{:02x}", h[30], h[31]);
                let hex_tail_opt = |h: &Option<[u8; 32]>| {
                    h.as_ref().map(hex_tail).unwrap_or_else(|| "<none>".into())
                };
                let oldest = candidate.iter().next();
                let newest = candidate.iter().next_back();
                let oldest_prev_in_ancestors = oldest
                    .and_then(|e| e.prev_hash)
                    .map(|p| adopted_ancestors.contains(&p))
                    .unwrap_or(false);
                info!(
                    node_id = %self.node_id,
                    %peer_id,
                    peer_tip_block_no = candidate_tip.block_no,
                    adopted_block_no = adopted_bn,
                    adopted_hash = hex_tail(&adopted_hash),
                    peer_chain_len = candidate.len(),
                    adopted_ancestors_len = adopted_ancestors.len(),
                    oldest_block_no = oldest.map(|e| e.block_no),
                    oldest_hash = oldest.map(|e| hex_tail(&e.hash)),
                    oldest_prev_hash = hex_tail_opt(&oldest.and_then(|e| e.prev_hash)),
                    oldest_prev_in_ancestors,
                    newest_block_no = newest.map(|e| e.block_no),
                    newest_hash = newest.map(|e| hex_tail(&e.hash)),
                    newest_prev_hash = hex_tail_opt(&newest.and_then(|e| e.prev_hash)),
                    "select_chain: orphan — no common ancestor found"
                );
                return SelectionDecision::OrphanCandidate {
                    peer_id,
                    tip_block_no: candidate_tip.block_no,
                };
            }
        };

        let replay: Vec<(Point, [u8; 32])> = replay_rev
            .into_iter()
            .rev()
            .map(|e| (e.point.clone(), e.hash))
            .collect();

        let missing: Vec<Point> = replay
            .iter()
            .filter(|(_, h)| !self.validated.contains(h) && !self.block_cache.contains_key(h))
            .map(|(p, _)| p.clone())
            .collect();

        let anchor_point = candidate.anchor().and_then(|a| {
            let oldest_prev = candidate.iter().next().and_then(|e| e.prev_hash);
            if a.hash == ancestor && oldest_prev != Some(ancestor) {
                Some(a.point.clone())
            } else {
                None
            }
        });

        if missing.is_empty() {
            let replay_hashes: Vec<[u8; 32]> = replay.iter().map(|(_, h)| *h).collect();
            if let Some(&last_hash) = replay_hashes.last() {
                let walk_result = self.walk_ancestors_hybrid(last_hash);
                let walk: HashSet<[u8; 32]> = walk_result.chain.iter().copied().collect();
                let all_on_chain = replay_hashes.iter().all(|h| walk.contains(h));
                if !all_on_chain {
                    tracing::debug!(
                        node_id = %self.node_id,
                        %peer_id,
                        tip_block_no = candidate_tip.block_no,
                        replay_len = replay_hashes.len(),
                        "select_chain: non-contiguous replay (mixed forks); skipping peer"
                    );
                    return SelectionDecision::OrphanCandidate {
                        peer_id,
                        tip_block_no: candidate_tip.block_no,
                    };
                }
                let reaches_ancestor = if ancestor == [0u8; 32] {
                    walk_result.reached_origin
                } else {
                    walk.contains(&ancestor)
                };
                if !reaches_ancestor {
                    info!(
                        node_id = %self.node_id,
                        %peer_id,
                        tip_block_no = candidate_tip.block_no,
                        ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                        "select_chain: fork mismatch (replay doesn't reach ancestor); skipping peer"
                    );
                    return SelectionDecision::OrphanCandidate {
                        peer_id,
                        tip_block_no: candidate_tip.block_no,
                    };
                }
            }
            SelectionDecision::Switched {
                peer_id,
                ancestor,
                replay: replay_hashes,
                tip_block_no: candidate_tip.block_no,
            }
        } else {
            SelectionDecision::WaitingForBlocks {
                peer_id,
                ancestor,
                anchor_point,
                missing,
                tip_block_no: candidate_tip.block_no,
            }
        }
    }

    /// Try to switch to a specific block as chain tip.  Walks back
    /// through chain_tree from `tip_hash` to `adopted_tip` and returns
    /// the contiguous prefix of cached blocks as a replay sequence.
    #[allow(clippy::type_complexity)]
    pub fn try_switch_to(
        &self,
        tip_hash: [u8; 32],
    ) -> Result<([u8; 32], Vec<[u8; 32]>), Option<Point>> {
        let adopted = self.adopted_tip_hash.unwrap_or([0u8; 32]);
        if tip_hash == adopted {
            return Err(None);
        }
        let tip_bn = match self.chain_tree.block_number(&tip_hash) {
            Some(bn) => bn,
            None => return Err(None),
        };
        let adopted_bn = self
            .adopted_tip_hash
            .and_then(|h| self.chain_tree.block_number(&h))
            .unwrap_or(0);
        if !is_better_tip(tip_bn, &tip_hash, adopted_bn, &adopted) {
            return Err(None);
        }
        let walk = self.chain_tree.ancestors(tip_hash);
        let adopted_ancestors: HashSet<[u8; 32]> = self
            .adopted_tip_hash
            .map(|h| self.chain_tree.ancestors(h).into_iter().collect())
            .unwrap_or_default();
        let ancestor_pos = walk
            .iter()
            .position(|h| *h == adopted || adopted_ancestors.contains(h));
        let ancestor_pos = match ancestor_pos {
            Some(p) => p,
            None if self.adopted_tip_hash.is_none() => match walk.last() {
                Some(h) if self.chain_tree.prev_hash(h).is_none() => walk.len(),
                _ => {
                    let gap_hash = walk.last().copied();
                    let gap_point = gap_hash.and_then(|h| self.chain_tree.point(&h).cloned());
                    return Err(gap_point);
                }
            },
            None => {
                let gap_hash = walk.last().copied();
                let gap_point = gap_hash.and_then(|h| self.chain_tree.point(&h).cloned());
                return Err(gap_point);
            }
        };
        let ancestor = if ancestor_pos < walk.len() {
            walk[ancestor_pos]
        } else {
            [0u8; 32]
        };
        let replay: Vec<[u8; 32]> = walk[..ancestor_pos].iter().rev().copied().collect();
        if replay.is_empty() {
            return Err(None);
        }
        let prefix: Vec<[u8; 32]> = replay
            .into_iter()
            .take_while(|h| {
                !self.in_flight_validation.contains(h)
                    && (self.validated.contains(h) || self.block_cache.contains_key(h))
            })
            .collect();
        if prefix.is_empty() {
            return Err(None);
        }
        Ok((ancestor, prefix))
    }

    // -- Internal effect-emitting helpers -----------------------------------

    fn evict_stale_in_flight(&mut self, now: Instant) {
        self.in_flight
            .retain(|_, started| now.duration_since(*started) < IN_FLIGHT_TTL);
    }

    fn evaluate_and_fetch_internal(&mut self, now: Instant, fx: &mut Vec<PraosEffect>) {
        let mut skip: HashSet<PeerId> = self
            .orphan_cooldown
            .iter()
            .filter(|(_, until)| **until > now)
            .map(|(p, _)| *p)
            .collect();
        self.orphan_cooldown.retain(|_, until| *until > now);
        // Peers that recently failed a fetch are excluded too — gives
        // the fetch policy room to pick someone else.
        for (p, until) in &self.block_fetch_cooldown {
            if *until > now {
                skip.insert(*p);
            }
        }
        self.block_fetch_cooldown.retain(|_, until| *until > now);

        loop {
            match self.select_chain_once(&skip) {
                SelectionDecision::NoBetterChain => return,
                SelectionDecision::OrphanCandidate {
                    peer_id,
                    tip_block_no,
                } => {
                    if let Some(chain) = self.peer_chains.get_mut(&peer_id) {
                        chain.clear_entries();
                    }
                    let already_cooling = self.orphan_cooldown.contains_key(&peer_id);
                    self.orphan_cooldown.insert(peer_id, now + ORPHAN_COOLDOWN);
                    skip.insert(peer_id);
                    if !already_cooling {
                        info!(
                            node_id = %self.node_id,
                            %peer_id,
                            tip_block_no,
                            "select_chain: orphan, clearing entries and requesting re-intersection"
                        );
                        fx.push(PraosEffect::ReIntersect { peer_id });
                    }
                    continue;
                }
                SelectionDecision::Switched {
                    peer_id,
                    ancestor,
                    replay,
                    tip_block_no,
                } => {
                    info!(
                        node_id = %self.node_id,
                        %peer_id,
                        tip_block_no,
                        replay_len = replay.len(),
                        ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                        "select_chain: fork switch"
                    );
                    self.execute_switch_internal(ancestor, replay, fx);
                    return;
                }
                SelectionDecision::WaitingForBlocks {
                    peer_id,
                    ancestor,
                    anchor_point,
                    missing,
                    tip_block_no,
                    ..
                } => {
                    debug!(
                        node_id = %self.node_id,
                        %peer_id,
                        tip_block_no,
                        missing_len = missing.len(),
                        has_anchor_gap = anchor_point.is_some(),
                        ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                        "select_chain: fetching missing blocks"
                    );
                    let now2 = now;
                    self.issue_fetch_internal(missing, anchor_point, Some(peer_id), now2, fx);
                    return;
                }
            }
        }
    }

    fn try_switch_and_execute_internal(
        &mut self,
        tip_hash: [u8; 32],
        fx: &mut Vec<PraosEffect>,
    ) -> bool {
        if let Ok((ancestor, replay)) = self.try_switch_to(tip_hash) {
            info!(
                node_id = %self.node_id,
                replay_len = replay.len(),
                ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                "chain selection: switching to stored blocks"
            );
            self.execute_switch_internal(ancestor, replay, fx);
            true
        } else {
            false
        }
    }

    fn execute_switch_internal(
        &mut self,
        ancestor: [u8; 32],
        replay: Vec<[u8; 32]>,
        fx: &mut Vec<PraosEffect>,
    ) {
        let needs_rollback = ancestor != [0u8; 32] || self.adopted_tip_hash.is_some();
        if needs_rollback && self.queued_validator_tip != Some(ancestor) {
            if ancestor == [0u8; 32] {
                fx.push(PraosEffect::ValidatorRollback {
                    target: Point::Origin,
                });
                self.queued_validator_tip = None;
                self.adopted_tip_hash = None;
            } else {
                let ancestor_point = match self.chain_tree.point(&ancestor) {
                    Some(p) => p.clone(),
                    None => {
                        warn!(
                            node_id = %self.node_id,
                            ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                            "select_chain: ancestor point not in chain_tree; aborting switch"
                        );
                        return;
                    }
                };
                fx.push(PraosEffect::ValidatorRollback {
                    target: ancestor_point,
                });
                self.queued_validator_tip = Some(ancestor);
                self.adopted_tip_hash = Some(ancestor);
            }
        }
        for hash in replay {
            let (point, body, prev_hash) = match self.block_cache.get(&hash) {
                Some(cb) => (cb.point.clone(), cb.body.clone(), cb.prev_hash),
                None => {
                    warn!(
                        node_id = %self.node_id,
                        hash = format!("{:02x}{:02x}", hash[30], hash[31]),
                        "select_chain: replay block not in cache; aborting switch"
                    );
                    return;
                }
            };
            self.submit_for_validation_internal(point, body, prev_hash, fx);
        }
    }

    fn submit_for_validation_internal(
        &mut self,
        point: Point,
        body: Vec<u8>,
        prev_hash: Option<[u8; 32]>,
        fx: &mut Vec<PraosEffect>,
    ) {
        let new_hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        if prev_hash != self.queued_validator_tip {
            if let Some(parent_hash) = prev_hash {
                if let Some(parent_point) = self.chain_tree.point(&parent_hash).cloned() {
                    fx.push(PraosEffect::ValidatorRollback {
                        target: parent_point,
                    });
                    self.queued_validator_tip = Some(parent_hash);
                } else {
                    let hex = |h: &[u8; 32]| format!("{:02x}{:02x}", h[30], h[31]);
                    tracing::debug!(
                        node_id = %self.node_id,
                        parent = hex(&parent_hash),
                        queued_tip = self
                            .queued_validator_tip
                            .as_ref()
                            .map(|h| format!("{:02x}{:02x}", h[30], h[31]))
                            .as_deref()
                            .unwrap_or("<none>"),
                        block = format!("{}", point),
                        "parent not in chain_tree — skipping rollback"
                    );
                }
            }
        }
        fx.push(PraosEffect::ValidatorApply {
            point: point.clone(),
            body,
            prev_hash,
        });
        self.queued_validator_tip = Some(new_hash);
        self.adopted_tip_hash = Some(new_hash);
        self.in_flight_validation.insert(new_hash);
    }

    fn issue_fetch_internal(
        &mut self,
        missing: Vec<Point>,
        anchor_point: Option<Point>,
        peer_id: Option<PeerId>,
        now: Instant,
        fx: &mut Vec<PraosEffect>,
    ) {
        if missing.is_empty() {
            return;
        }
        self.evict_stale_in_flight(now);

        // Only fetch blocks that aren't already part of an outstanding
        // request.  `in_flight` is keyed per block — every block we ask
        // for is recorded below and removed as it arrives (see
        // `on_block_received`) — so filtering here collapses the request
        // to the *frontier* gap.  Without it, every ChainSync roll-forward
        // re-issues a range from the anchor to the new tip, re-fetching the
        // whole not-yet-validated backlog; during deep catch-up (a follower
        // thousands of blocks behind a live peer) that amplifies block
        // traffic super-linearly.
        let to_fetch: Vec<Point> = missing
            .iter()
            .filter(|p| !self.in_flight.contains_key(p))
            .cloned()
            .collect();
        if to_fetch.is_empty() {
            return;
        }

        // The BlockFetch range lower bound must be a real block point.
        // A standard Cardano server rejects — and resets the bearer on —
        // a range anchored at Origin, since genesis carries no block.
        // Use the supplied anchor only when the frontier still begins at
        // the oldest missing block (no in-flight prefix was filtered off);
        // otherwise start at the first block we actually still need so the
        // range doesn't overlap an outstanding request.
        let frontier_is_oldest = to_fetch.first() == missing.first();
        let from = match anchor_point {
            Some(p) if frontier_is_oldest && !matches!(p, Point::Origin) => p,
            _ => to_fetch.first().unwrap().clone(),
        };
        let to = to_fetch.last().unwrap().clone();

        // Record every block in the issued range as in flight so later
        // roll-forwards skip it until it arrives or its marker goes stale.
        for p in &to_fetch {
            self.in_flight.insert(p.clone(), now);
        }
        let peers = self.choose_block_fetch_peers(&to, peer_id);
        debug!(
            node_id = %self.node_id,
            %from,
            %to,
            fetch_len = to_fetch.len(),
            peer_count = peers.len(),
            "fetching missing chain blocks"
        );
        fx.push(PraosEffect::FetchBlockRange { from, to, peers });
    }

    /// Resolve the candidate peer set for a Praos block fetch and run
    /// it through the configured [`BlockFetchPolicy`].
    ///
    /// `hint` is the peer whose chain selection drove us to this fetch
    /// — if its peer-chain still references the target point, it stays
    /// in the candidate pool; otherwise the candidate set is the union
    /// of every peer whose announced chain contains `point`.  The
    /// policy then picks one or more from that pool.
    fn choose_block_fetch_peers(&self, point: &Point, hint: Option<PeerId>) -> Vec<PeerId> {
        let mut candidates: Vec<PeerId> = self
            .peer_chains
            .iter()
            .filter(|(_, chain)| chain.iter().any(|e| e.point == *point))
            .map(|(p, _)| *p)
            .collect();
        // If the hint isn't already in the candidate set (the
        // triggering peer's chain may not extend to `point`), include
        // it as a fallback.
        if let Some(h) = hint {
            if !candidates.contains(&h) {
                candidates.push(h);
            }
        }
        self.block_policy
            .pick(point, &candidates, self.rtt.as_ref())
    }
}

// ---------------------------------------------------------------------------
// Logical header info passed in by the I/O wrapper
// ---------------------------------------------------------------------------

/// Header metadata extracted from a wire-format header by the I/O
/// wrapper.  This crate never parses headers itself.
#[derive(Debug, Clone, Default)]
pub struct ParsedHeaderInfo {
    pub block_number: u64,
    pub slot: u64,
    pub prev_hash: Option<[u8; 32]>,
    /// EB hash this header announces, if any (CIP-0164 Leios extension).
    pub announced_eb_hash: Option<[u8; 32]>,
    /// CIP-0164 Leios extension: whether this RB certifies the parent
    /// RB's announced EB.  The EB being certified is the parent's
    /// `announced_eb_hash`; chain context (`parent_announced_eb`)
    /// resolves the hash at apply time.
    pub certified_eb: bool,
    /// Producer identity (issuer verification key in real Cardano;
    /// `NodeId` bytes in sim).  Used for CIP-0164 RB-header
    /// equivocation detection: two distinct header hashes with the
    /// same `(slot, issuer)` tuple are an equivocation, and honest
    /// voters must abstain from voting on any EB associated with
    /// that slot.  Empty bytes disable detection for this header
    /// (preserves behavior for callers that haven't populated it).
    pub issuer: Vec<u8>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn h(seed: u8) -> [u8; 32] {
        [seed; 32]
    }

    fn pt(slot: u64, hash_seed: u8) -> Point {
        Point::Specific {
            slot,
            hash: h(hash_seed),
        }
    }

    fn hi(block_number: u64, slot: u64, prev_seed: Option<u8>) -> ParsedHeaderInfo {
        ParsedHeaderInfo {
            announced_eb_hash: None,
            block_number,
            slot,
            prev_hash: prev_seed.map(h),
            certified_eb: false,
            issuer: Vec::new(),
        }
    }

    fn fresh() -> PraosState {
        PraosState::new("test".to_string(), 100)
    }

    /// Pre-populate chain_tree + block_cache + validated as if the block
    /// had been fetched, applied, and adopted.  Avoids driving every
    /// scenario through the public API.
    fn install_validated_block(
        state: &mut PraosState,
        slot: u64,
        seed: u8,
        block_no: u64,
        prev_seed: Option<u8>,
    ) {
        let hash = h(seed);
        let point = pt(slot, seed);
        let prev_hash = prev_seed.map(h);
        state.chain_tree.insert(
            hash,
            point.clone(),
            block_no,
            slot,
            prev_hash,
            0,
            None,
            false,
        );
        state.block_cache.insert(
            hash,
            CachedBlock {
                point,
                block_no,
                prev_hash,
                header: vec![],
                body: vec![],
                announced_eb_hash: None,
                certified_eb: false,
            },
        );
        state.validated.insert(hash);
    }

    // -- Construction & queries ------------------------------------------

    #[test]
    fn new_state_is_empty() {
        let s = fresh();
        assert_eq!(s.tip_hash(), None);
        assert_eq!(s.next_block_number(), 1);
        assert_eq!(s.local_tip(), None);
    }

    #[test]
    fn peer_chain_cap_floor_is_64() {
        let small = PraosState::new("test".to_string(), 0);
        assert_eq!(small.peer_chain_cap(), 64);
        let large = PraosState::new("test".to_string(), 1000);
        assert_eq!(large.peer_chain_cap(), 2000);
    }

    #[test]
    fn next_block_number_extends_adopted() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 5, None);
        s.adopted_tip_hash = Some(h(1));
        assert_eq!(s.next_block_number(), 6);
    }

    #[test]
    fn local_tip_returns_chain_tree_best() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 5, None);
        let (point, block_no) = s.local_tip().expect("tip set after insert");
        assert_eq!(point, pt(100, 1));
        assert_eq!(block_no, 5);
    }

    #[test]
    fn chain_tree_snapshot_with_tip() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 5, None);
        s.adopted_tip_hash = Some(h(1));
        let (entries, block_no, tip_hex) = s.chain_tree_snapshot(|_| None);
        assert!(!entries.is_empty());
        assert_eq!(block_no, Some(5));
        assert!(tip_hex.is_some());
    }

    // -- Peer-event mutations (no effects) -------------------------------

    #[test]
    fn record_peer_tip_appends_entry() {
        let mut s = fresh();
        let pid = PeerId(7);
        s.record_peer_tip(pid, pt(100, 1), 1, 1, h(1), 100, None);
        let chain = s.peer_chains.get(&pid).expect("peer chain present");
        assert_eq!(chain.tip().unwrap().block_no, 1);
    }

    #[test]
    fn record_peer_intersection_sets_anchor() {
        let mut s = fresh();
        let pid = PeerId(7);
        s.record_peer_intersection(pid, pt(50, 1));
        let chain = s.peer_chains.get(&pid).expect("peer chain present");
        assert!(chain.anchor().is_some());
    }

    #[test]
    fn record_peer_rollback_truncates() {
        let mut s = fresh();
        let pid = PeerId(7);
        s.record_peer_tip(pid, pt(100, 1), 1, 1, h(1), 100, None);
        s.record_peer_tip(pid, pt(101, 2), 2, 2, h(2), 101, Some(h(1)));
        s.record_peer_rollback(pid, &pt(100, 1));
        let chain = s.peer_chains.get(&pid).unwrap();
        assert_eq!(chain.tip().unwrap().block_no, 1);
    }

    #[test]
    fn record_peer_disconnected_clears_chain_and_cooldown() {
        let mut s = fresh();
        let pid = PeerId(7);
        s.record_peer_tip(pid, pt(100, 1), 1, 1, h(1), 100, None);
        s.orphan_cooldown
            .insert(pid, Instant::now() + Duration::from_secs(60));
        s.record_peer_disconnected(pid);
        assert!(!s.peer_chains.contains_key(&pid));
        assert!(!s.orphan_cooldown.contains_key(&pid));
    }

    // -- CIP-0164 RB-header equivocation detection ----------------------

    fn parsed_with_issuer(slot: u64, issuer: u8) -> ParsedHeaderInfo {
        ParsedHeaderInfo {
            block_number: slot,
            slot,
            prev_hash: None,
            announced_eb_hash: None,
            certified_eb: false,
            issuer: vec![issuer; 4],
        }
    }

    #[test]
    fn two_distinct_headers_same_slot_issuer_flag_slot() {
        let mut s = fresh();
        s.on_block_received(
            pt(100, 1),
            vec![],
            vec![],
            Some(parsed_with_issuer(100, 0xAA)),
            0,
        );
        s.on_block_received(
            pt(100, 2),
            vec![],
            vec![],
            Some(parsed_with_issuer(100, 0xAA)),
            0,
        );
        assert!(s.is_equivocating_slot(100));
        assert!(s.equivocating_rb_slots.contains(&100));
    }

    #[test]
    fn distinct_headers_same_slot_different_issuers_no_flag() {
        // Two different producers winning the same slot via VRF is a
        // legitimate Praos fork — not equivocation by CIP-0164.
        let mut s = fresh();
        s.on_block_received(
            pt(100, 1),
            vec![],
            vec![],
            Some(parsed_with_issuer(100, 0xAA)),
            0,
        );
        s.on_block_received(
            pt(100, 2),
            vec![],
            vec![],
            Some(parsed_with_issuer(100, 0xBB)),
            0,
        );
        assert!(!s.is_equivocating_slot(100));
    }

    #[test]
    fn empty_issuer_disables_detection() {
        // Pre-issuer callers (issuer = Vec::new()) get no-op detection,
        // preserving legacy behavior.
        let mut s = fresh();
        s.on_block_received(pt(100, 1), vec![], vec![], Some(hi(100, 100, None)), 0);
        s.on_block_received(pt(100, 2), vec![], vec![], Some(hi(100, 100, None)), 0);
        assert!(!s.is_equivocating_slot(100));
    }

    #[test]
    fn duplicate_header_hash_same_issuer_does_not_flag() {
        // Same hash arriving twice (e.g., from two peers) isn't
        // equivocation — it's the same header.
        let mut s = fresh();
        s.on_block_received(
            pt(100, 1),
            vec![],
            vec![],
            Some(parsed_with_issuer(100, 0xAA)),
            0,
        );
        // Second on_block_received with the same hash is a no-op via
        // the block_cache dedup; manually probe the tracker invariant.
        s.note_header_for_equivocation(100, &[0xAA; 4], h(1));
        assert!(!s.is_equivocating_slot(100));
    }

    #[test]
    fn self_produced_equivocation_flags_slot() {
        // A producer that registers two distinct self-produced
        // headers at the same slot equivocates against itself; the
        // tracker honors that.
        let mut s = fresh();
        s.register_self_produced(
            pt(100, 1),
            vec![],
            vec![],
            Some(parsed_with_issuer(100, 0xAA)),
            0,
        );
        s.register_self_produced(
            pt(100, 2),
            vec![],
            vec![],
            Some(parsed_with_issuer(100, 0xAA)),
            0,
        );
        assert!(s.is_equivocating_slot(100));
    }

    // -- Self-production --------------------------------------------------

    #[test]
    fn register_self_produced_emits_validator_apply() {
        let mut s = fresh();
        let fx = s.register_self_produced(
            pt(100, 1),
            vec![0xAA],
            vec![0xBB],
            Some(hi(1, 100, None)),
            0,
        );
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            PraosEffect::ValidatorApply {
                point,
                body,
                prev_hash,
            } => {
                assert_eq!(*point, pt(100, 1));
                assert_eq!(body, &vec![0xBB]);
                assert_eq!(*prev_hash, None);
            }
            other => panic!("expected ValidatorApply, got {other:?}"),
        }
        assert_eq!(s.adopted_tip_hash, Some(h(1)));
        assert_eq!(s.queued_validator_tip, Some(h(1)));
        assert!(s.in_flight_validation.contains(&h(1)));
        assert!(s.self_produced.contains(&pt(100, 1)));
    }

    #[test]
    fn register_self_produced_opaque_header_skips_chain_tree() {
        let mut s = fresh();
        let fx = s.register_self_produced(pt(100, 1), vec![0xAA], vec![0xBB], None, 0);
        assert_eq!(fx.len(), 1);
        assert!(matches!(fx[0], PraosEffect::ValidatorApply { .. }));
        assert!(s.chain_tree.block_number(&h(1)).is_none());
    }

    #[test]
    fn adopted_tip_accessors_track_announced_eb() {
        let mut s = fresh();
        let mut info = hi(1, 100, None);
        info.announced_eb_hash = Some(h(0xEB));
        s.register_self_produced(pt(100, 1), vec![0xAA], vec![0xBB], Some(info), 0);
        // Without note_header_first_seen, the accessor falls back to
        // the RB's own slot.
        assert_eq!(s.adopted_tip_header_arrival_slot(), Some(100));
        assert_eq!(s.adopted_tip_announced_eb(), Some(h(0xEB)));
    }

    #[test]
    fn adopted_tip_accessors_none_when_no_tip() {
        let s = fresh();
        assert_eq!(s.adopted_tip_header_arrival_slot(), None);
        assert_eq!(s.adopted_tip_announced_eb(), None);
    }

    #[test]
    fn adopted_tip_announced_eb_none_for_pre_leios_header() {
        let mut s = fresh();
        s.register_self_produced(
            pt(100, 1),
            vec![0xAA],
            vec![0xBB],
            Some(hi(1, 100, None)),
            0,
        );
        // hi() defaults announced_eb_hash to None.
        assert_eq!(s.adopted_tip_announced_eb(), None);
    }

    #[test]
    fn note_header_first_seen_is_used_for_arrival() {
        let mut s = fresh();
        s.register_self_produced(
            pt(100, 1),
            vec![0xAA],
            vec![0xBB],
            Some(hi(1, 100, None)),
            0,
        );
        // Wrapper observed the header at slot 102 (e.g., body arrived
        // 2 slots after the RB's own slot via fetch).
        s.note_header_first_seen(h(1), 102);
        assert_eq!(s.adopted_tip_header_arrival_slot(), Some(102));
    }

    #[test]
    fn note_header_first_seen_is_idempotent() {
        let mut s = fresh();
        s.register_self_produced(
            pt(100, 1),
            vec![0xAA],
            vec![0xBB],
            Some(hi(1, 100, None)),
            0,
        );
        s.note_header_first_seen(h(1), 105);
        // Subsequent calls don't overwrite — only the first arrival counts.
        s.note_header_first_seen(h(1), 200);
        assert_eq!(s.adopted_tip_header_arrival_slot(), Some(105));
    }

    #[test]
    fn register_self_produced_origin_point_is_noop() {
        let mut s = fresh();
        let fx = s.register_self_produced(Point::Origin, vec![], vec![], Some(hi(1, 0, None)), 0);
        assert!(fx.is_empty());
        assert!(s.self_produced.contains(&Point::Origin));
    }

    // -- Validation outcomes ---------------------------------------------

    #[test]
    fn on_block_applied_emits_inject_block() {
        let mut s = fresh();
        s.register_self_produced(
            pt(100, 1),
            vec![0xAA],
            vec![0xBB],
            Some(hi(1, 100, None)),
            0,
        );
        let fx = s.on_block_applied(pt(100, 1), Instant::now());
        assert!(matches!(fx[0], PraosEffect::InjectBlock { .. }));
        assert!(s.validated.contains(&h(1)));
        assert_eq!(s.last_validated_tip, Some(h(1)));
    }

    #[test]
    fn on_block_applied_uncached_block_is_noop() {
        let mut s = fresh();
        let fx = s.on_block_applied(pt(100, 1), Instant::now());
        assert!(fx.is_empty());
        assert!(!s.validated.contains(&h(1)));
    }

    #[test]
    fn on_block_applied_prunes_below_k() {
        let mut s = PraosState::new("test".to_string(), 2); // k = 2
        install_validated_block(&mut s, 100, 1, 1, None);
        install_validated_block(&mut s, 101, 2, 2, Some(1));
        install_validated_block(&mut s, 102, 3, 3, Some(2));
        // Stage block 4 in cache (not yet validated).
        s.chain_tree
            .insert(h(4), pt(103, 4), 4, 103, Some(h(3)), 0, None, false);
        s.block_cache.insert(
            h(4),
            CachedBlock {
                point: pt(103, 4),
                block_no: 4,
                prev_hash: Some(h(3)),
                header: vec![],
                body: vec![],
                announced_eb_hash: None,
                certified_eb: false,
            },
        );
        s.adopted_tip_hash = Some(h(4));

        let _ = s.on_block_applied(pt(103, 4), Instant::now());

        // bn=4 - k=2 = 2 ⇒ blocks with bn < 2 dropped (block 1 only).
        assert!(!s.block_cache.contains_key(&h(1)));
        assert!(s.block_cache.contains_key(&h(2)));
        assert!(s.block_cache.contains_key(&h(3)));
        assert!(s.block_cache.contains_key(&h(4)));
    }

    #[test]
    fn on_block_apply_failed_rewinds_to_last_validated() {
        let mut s = fresh();
        s.register_self_produced(
            pt(100, 1),
            vec![0xAA],
            vec![0xBB],
            Some(hi(1, 100, None)),
            0,
        );
        let _ = s.on_block_applied(pt(100, 1), Instant::now());
        s.register_self_produced(
            pt(101, 2),
            vec![0xAA],
            vec![0xBC],
            Some(hi(2, 101, Some(1))),
            0,
        );
        s.on_block_apply_failed(pt(101, 2), "ledger error".to_string());
        assert_eq!(s.queued_validator_tip, Some(h(1)));
        assert_eq!(s.adopted_tip_hash, Some(h(1)));
        assert!(!s.validated.contains(&h(2)));
    }

    #[test]
    fn on_block_rolled_back_origin_clears_last_validated() {
        let mut s = fresh();
        s.last_validated_tip = Some(h(1));
        let fx = s.on_block_rolled_back(Point::Origin);
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            PraosEffect::InjectRollback { target } => assert_eq!(*target, Point::Origin),
            other => panic!("expected InjectRollback, got {other:?}"),
        }
        assert_eq!(s.last_validated_tip, None);
    }

    #[test]
    fn on_block_rolled_back_specific_emits_inject_rollback() {
        let mut s = fresh();
        let fx = s.on_block_rolled_back(pt(50, 9));
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            PraosEffect::InjectRollback { target } => assert_eq!(*target, pt(50, 9)),
            other => panic!("expected InjectRollback, got {other:?}"),
        }
        assert_eq!(s.last_validated_tip, Some(h(9)));
    }

    // -- on_block_received ------------------------------------------------

    #[test]
    fn on_block_received_dedups_via_cache() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 1, None);
        let fx = s.on_block_received(pt(100, 1), vec![], vec![], None, 0);
        assert!(fx.is_empty());
    }

    #[test]
    fn on_block_received_origin_point_is_noop() {
        let mut s = fresh();
        let fx = s.on_block_received(Point::Origin, vec![], vec![], None, 0);
        assert!(fx.is_empty());
    }

    #[test]
    fn on_block_received_inserts_and_emits_validator_apply() {
        let mut s = fresh();
        let fx = s.on_block_received(
            pt(100, 1),
            vec![0xAA],
            vec![0xBB],
            Some(hi(1, 100, None)),
            0,
        );
        assert!(fx
            .iter()
            .any(|e| matches!(e, PraosEffect::ValidatorApply { .. })));
        assert!(s.block_cache.contains_key(&h(1)));
        assert_eq!(s.chain_tree.block_number(&h(1)), Some(1));
    }

    #[test]
    fn on_block_received_opaque_header_no_chain_tree_insert() {
        let mut s = fresh();
        let fx = s.on_block_received(pt(100, 1), vec![0xAA], vec![0xBB], None, 0);
        // No chain_tree entry, so try_switch fails silently.
        assert!(fx.is_empty());
        assert!(s.chain_tree.block_number(&h(1)).is_none());
        assert!(s.block_cache.contains_key(&h(1)));
    }

    // -- Chain selection (pure) ------------------------------------------

    #[test]
    fn select_chain_no_better_when_no_peers() {
        let s = fresh();
        let decision = s.select_chain_once(&HashSet::new());
        assert!(matches!(decision, SelectionDecision::NoBetterChain));
    }

    #[test]
    fn select_chain_switched_when_peer_ahead_and_cached() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 1, None);
        s.adopted_tip_hash = Some(h(1));
        // Block 2 cached and validated but not yet adopted.
        install_validated_block(&mut s, 101, 2, 2, Some(1));

        let pid = PeerId(7);
        s.record_peer_tip(pid, pt(101, 2), 2, 2, h(2), 101, Some(h(1)));

        match s.select_chain_once(&HashSet::new()) {
            SelectionDecision::Switched {
                peer_id,
                ancestor,
                replay,
                tip_block_no,
            } => {
                assert_eq!(peer_id, pid);
                assert_eq!(ancestor, h(1));
                assert_eq!(replay, vec![h(2)]);
                assert_eq!(tip_block_no, 2);
            }
            other => panic!("expected Switched, got {other:?}"),
        }
    }

    #[test]
    fn select_chain_waiting_when_blocks_missing() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 1, None);
        s.adopted_tip_hash = Some(h(1));

        let pid = PeerId(7);
        // Peer announces block 2 (prev=h(1)) but we don't have it cached.
        s.record_peer_tip(pid, pt(101, 2), 2, 2, h(2), 101, Some(h(1)));

        match s.select_chain_once(&HashSet::new()) {
            SelectionDecision::WaitingForBlocks {
                peer_id,
                ancestor,
                missing,
                tip_block_no,
                ..
            } => {
                assert_eq!(peer_id, pid);
                assert_eq!(ancestor, h(1));
                assert_eq!(missing, vec![pt(101, 2)]);
                assert_eq!(tip_block_no, 2);
            }
            other => panic!("expected WaitingForBlocks, got {other:?}"),
        }
    }

    #[test]
    fn select_chain_orphan_when_no_common_ancestor() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 1, None);
        s.adopted_tip_hash = Some(h(1));

        let pid = PeerId(7);
        // Peer chain references a parent we've never heard of.
        s.record_peer_tip(pid, pt(200, 99), 5, 5, h(99), 200, Some(h(88)));

        assert!(matches!(
            s.select_chain_once(&HashSet::new()),
            SelectionDecision::OrphanCandidate { .. }
        ));
    }

    #[test]
    fn select_chain_genesis_rooted_fork_is_not_orphan() {
        // Local node has adopted block 1 with hash h(0xFF).  A peer
        // announces a competing block 1 with hash h(1) and
        // prev_hash=None (rooted at genesis).  The peer's tip wins the
        // `is_better_tip` comparison (lower hash at the same height) and
        // the fork's only entry roots at genesis — so we should treat
        // genesis as the common ancestor and request the peer's body,
        // not declare the chain an orphan.
        let mut s = fresh();
        install_validated_block(&mut s, 100, 0xFF, 1, None);
        s.adopted_tip_hash = Some(h(0xFF));

        let pid = PeerId(7);
        s.record_peer_tip(pid, pt(100, 1), 1, 1, h(1), 100, None);

        match s.select_chain_once(&HashSet::new()) {
            SelectionDecision::WaitingForBlocks {
                peer_id,
                ancestor,
                missing,
                tip_block_no,
                ..
            } => {
                assert_eq!(peer_id, pid);
                assert_eq!(ancestor, [0u8; 32]);
                assert_eq!(missing, vec![pt(100, 1)]);
                assert_eq!(tip_block_no, 1);
            }
            other => panic!("expected WaitingForBlocks, got {other:?}"),
        }
    }

    #[test]
    fn select_chain_skip_filters_peers() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 1, None);
        s.adopted_tip_hash = Some(h(1));
        install_validated_block(&mut s, 101, 2, 2, Some(1));

        let pid = PeerId(7);
        s.record_peer_tip(pid, pt(101, 2), 2, 2, h(2), 101, Some(h(1)));

        let mut skip = HashSet::new();
        skip.insert(pid);
        assert!(matches!(
            s.select_chain_once(&skip),
            SelectionDecision::NoBetterChain
        ));
    }

    // -- try_switch_to and walk_ancestors_hybrid -------------------------

    #[test]
    fn try_switch_to_self_returns_err_none() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 1, None);
        s.adopted_tip_hash = Some(h(1));
        assert!(matches!(s.try_switch_to(h(1)), Err(None)));
    }

    #[test]
    fn try_switch_to_unknown_returns_err_none() {
        let s = fresh();
        assert!(matches!(s.try_switch_to(h(99)), Err(None)));
    }

    #[test]
    fn walk_ancestors_hybrid_traverses_chain_tree() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 1, None);
        install_validated_block(&mut s, 101, 2, 2, Some(1));
        install_validated_block(&mut s, 102, 3, 3, Some(2));

        let walk = s.walk_ancestors_hybrid(h(3));
        assert_eq!(walk.chain, vec![h(3), h(2), h(1)]);
        assert!(walk.reached_origin);
    }

    #[test]
    fn walk_ancestors_hybrid_falls_back_to_block_cache() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 1, None);
        // Block 2 is cached but missing from chain_tree.
        s.block_cache.insert(
            h(2),
            CachedBlock {
                point: pt(101, 2),
                block_no: 2,
                prev_hash: Some(h(1)),
                header: vec![],
                body: vec![],
                announced_eb_hash: None,
                certified_eb: false,
            },
        );
        let walk = s.walk_ancestors_hybrid(h(2));
        assert_eq!(walk.chain, vec![h(2), h(1)]);
        assert!(walk.reached_origin);
    }

    #[test]
    fn walk_ancestors_hybrid_unknown_terminates() {
        let s = fresh();
        let walk = s.walk_ancestors_hybrid(h(99));
        assert_eq!(walk.chain, vec![h(99)]);
        assert!(!walk.reached_origin);
    }

    // -- Periodic + retry paths ------------------------------------------

    #[test]
    fn retry_select_chain_evicts_stale_in_flight() {
        let mut s = fresh();
        let stale = Instant::now() - IN_FLIGHT_TTL - Duration::from_secs(1);
        s.in_flight.insert(pt(100, 1), stale);
        let _ = s.retry_select_chain(Instant::now());
        assert!(s.in_flight.is_empty());
    }

    #[test]
    fn force_rollback_reanchors_and_abandons_suffix() {
        // Deliberate self-reorg: roll back `depth` blocks, abandon the
        // suffix, and emit InjectRollback so the served chain mirrors it.
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 1, None);
        install_validated_block(&mut s, 101, 2, 2, Some(1));
        install_validated_block(&mut s, 102, 3, 3, Some(2));
        install_validated_block(&mut s, 103, 4, 4, Some(3));
        install_validated_block(&mut s, 104, 5, 5, Some(4));
        s.adopted_tip_hash = Some(h(5));
        s.last_validated_tip = Some(h(5));

        let fx = s.force_rollback(2); // 5 -> 3

        assert_eq!(s.adopted_tip_hash, Some(h(3)), "re-anchored 2 blocks back");
        assert_eq!(
            s.chain_tree.best_tip_hash(),
            Some(h(3)),
            "abandoned suffix pruned; best tip is the target"
        );
        assert!(
            s.chain_tree.block_number(&h(4)).is_none(),
            "block 4 abandoned"
        );
        assert!(
            s.chain_tree.block_number(&h(5)).is_none(),
            "block 5 abandoned"
        );
        // Cache and validated set must also drop the suffix, otherwise the
        // on_block_received dedup would block re-adoption when a peer
        // re-offers blocks 4/5.
        assert!(
            !s.block_cache.contains_key(&h(4)),
            "block 4 evicted from cache"
        );
        assert!(
            !s.block_cache.contains_key(&h(5)),
            "block 5 evicted from cache"
        );
        assert!(
            s.block_cache.contains_key(&h(3)),
            "target block kept in cache"
        );
        assert!(
            !s.validated.contains(&h(4)),
            "block 4 cleared from validated"
        );
        assert!(
            !s.validated.contains(&h(5)),
            "block 5 cleared from validated"
        );
        assert!(
            s.validated.contains(&h(3)),
            "target block kept in validated"
        );
        match fx.as_slice() {
            [PraosEffect::InjectRollback { target }] => assert_eq!(*target, pt(102, 3)),
            other => panic!("expected single InjectRollback to block 3, got {other:?}"),
        }

        // Too-deep / zero rollbacks are no-ops.
        assert!(s.force_rollback(0).is_empty());
        assert!(s.force_rollback(999).is_empty());
    }

    #[test]
    fn select_chain_trusts_intersection_anchor_within_k() {
        // Reconnect-handover: the peer is on a divergent fork; our fragment
        // doesn't reach the fork point and adopted_ancestors is truncated,
        // but the ChainSync intersection anchor points at a real block we
        // hold, within k.  Trust it and switch (WaitingForBlocks), don't
        // declare orphan.
        let mut s = fresh(); // k = 100
                             // Adopted tip = block 10, but its parent (9) is absent → ancestors(10)
                             // = {10} (truncated, as after pruning).
        install_validated_block(&mut s, 110, 10, 10, Some(9));
        s.adopted_tip_hash = Some(h(10));
        // A real block 5 we hold — the would-be common ancestor, reorg depth 5.
        install_validated_block(&mut s, 105, 5, 5, Some(4));

        let pid = PeerId(7);
        s.record_peer_intersection(pid, pt(105, 5)); // anchor = block 5
                                                     // Peer fragment: divergent blocks 11, 12 (prev not in our ancestry).
        s.record_peer_tip(pid, pt(111, 11), 11, 11, h(11), 111, Some(h(99)));
        s.record_peer_tip(pid, pt(112, 12), 12, 12, h(12), 112, Some(h(11)));

        match s.select_chain_once(&HashSet::new()) {
            SelectionDecision::WaitingForBlocks {
                ancestor,
                anchor_point,
                ..
            } => {
                assert_eq!(ancestor, h(5), "trusts the intersection anchor as ancestor");
                assert_eq!(
                    anchor_point,
                    Some(pt(105, 5)),
                    "fetch range anchored at the intersection block"
                );
            }
            other => panic!("expected WaitingForBlocks (anchor-trust switch), got {other:?}"),
        }
    }

    #[test]
    fn select_chain_refuses_reorg_deeper_than_k() {
        // Same shape, but the intersection anchor is deeper than k below the
        // adopted tip → a settled-block reorg, which must be refused.
        let mut s = fresh(); // k = 100
        install_validated_block(&mut s, 300, 200, 200, Some(199));
        s.adopted_tip_hash = Some(h(200));
        install_validated_block(&mut s, 150, 50, 50, Some(49)); // depth 150 > k

        let pid = PeerId(7);
        s.record_peer_intersection(pid, pt(150, 50));
        s.record_peer_tip(pid, pt(301, 201), 201, 201, h(201), 301, Some(h(99)));

        assert!(
            matches!(
                s.select_chain_once(&HashSet::new()),
                SelectionDecision::OrphanCandidate { .. }
            ),
            "reorg of depth 150 > k=100 must be refused"
        );
    }

    #[test]
    fn retry_select_chain_keeps_fresh_in_flight() {
        let mut s = fresh();
        s.in_flight.insert(pt(100, 1), Instant::now());
        let _ = s.retry_select_chain(Instant::now());
        assert!(s.in_flight.contains_key(&pt(100, 1)));
    }

    #[test]
    fn on_block_fetch_failed_drops_in_flight() {
        let mut s = fresh();
        s.in_flight.insert(pt(100, 1), Instant::now());
        s.in_flight.insert(pt(101, 2), Instant::now());
        let now = Instant::now();
        let pid = PeerId(7);
        let _ = s.on_block_fetch_failed(pid, &pt(100, 1), &pt(101, 2), now);
        assert!(!s.in_flight.contains_key(&pt(100, 1)));
        assert!(!s.in_flight.contains_key(&pt(101, 2)));
        assert!(s.block_fetch_cooldown.contains_key(&pid));
    }

    #[test]
    fn block_fetch_cooldown_excludes_peer_from_selection() {
        let mut s = fresh();
        let pid = PeerId(3);
        s.block_fetch_cooldown
            .insert(pid, Instant::now() + Duration::from_secs(10));
        let mut fx = Vec::new();
        s.evaluate_and_fetch_internal(Instant::now(), &mut fx);
        // No fetch effects should target the cooled peer.  We can't
        // observe `skip` directly, but the cooldown's entry remains
        // (not yet expired) and `select_chain_once` would have been
        // called with it in `skip` — see `select_chain_skip_filters_peers`
        // for the underlying skip-set semantics.
        assert!(s.block_fetch_cooldown.contains_key(&pid));
    }

    // -- High-level handlers --------------------------------------------

    #[test]
    fn on_tip_advanced_better_peer_emits_fetch() {
        let mut s = fresh();
        let pid = PeerId(7);
        let fx = s.on_tip_advanced(
            pid,
            pt(100, 1),
            1,
            1,
            h(1),
            100,
            None,
            &[0xAA; 4],
            Instant::now(),
        );
        assert!(fx
            .iter()
            .any(|e| matches!(e, PraosEffect::FetchBlockRange { .. })));
    }

    #[test]
    fn deep_catch_up_does_not_refetch_in_flight_blocks() {
        // Regression: during catch-up, successive roll-forwards must fetch
        // only the new frontier block, not re-issue a range back to the
        // anchor.  The old behaviour re-fetched the whole not-yet-validated
        // backlog on every roll-forward, amplifying block traffic
        // super-linearly against a far-ahead peer.
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 1, None);
        s.adopted_tip_hash = Some(h(1));
        let now = Instant::now();
        let pid = PeerId(7);

        let range_of = |fx: &[PraosEffect]| {
            fx.iter().find_map(|e| match e {
                PraosEffect::FetchBlockRange { from, to, .. } => Some((from.clone(), to.clone())),
                _ => None,
            })
        };

        // First roll-forward: peer announces block 2 (prev = adopted block 1).
        let fx1 = s.on_tip_advanced(
            pid,
            pt(101, 2),
            2,
            2,
            h(2),
            101,
            Some(h(1)),
            &[0xAA; 4],
            now,
        );
        assert_eq!(
            range_of(&fx1),
            Some((pt(101, 2), pt(101, 2))),
            "first roll-forward fetches block 2"
        );
        assert!(s.in_flight.contains_key(&pt(101, 2)));

        // Second roll-forward BEFORE block 2 validates: peer announces block
        // 3 (prev = block 2).  Block 2 is still in flight, so the new fetch
        // must cover only block 3 — not the overlapping range [2, 3].
        let fx2 = s.on_tip_advanced(
            pid,
            pt(102, 3),
            3,
            3,
            h(3),
            102,
            Some(h(2)),
            &[0xAA; 4],
            now,
        );
        assert_eq!(
            range_of(&fx2),
            Some((pt(102, 3), pt(102, 3))),
            "second fetch must not re-include the in-flight block 2"
        );
    }

    #[test]
    fn on_peer_disconnected_with_no_others_emits_no_effects() {
        let mut s = fresh();
        let pid = PeerId(7);
        s.record_peer_tip(pid, pt(100, 1), 1, 1, h(1), 100, None);
        let fx = s.on_peer_disconnected(pid, Instant::now());
        assert!(fx.is_empty());
        assert!(!s.peer_chains.contains_key(&pid));
    }

    #[test]
    fn on_peer_rolled_back_truncates_and_re_evaluates() {
        let mut s = fresh();
        let pid = PeerId(7);
        s.record_peer_tip(pid, pt(100, 1), 1, 1, h(1), 100, None);
        s.record_peer_tip(pid, pt(101, 2), 2, 2, h(2), 101, Some(h(1)));
        let _ = s.on_peer_rolled_back(pid, &pt(100, 1), Instant::now());
        assert_eq!(s.peer_chains.get(&pid).unwrap().tip().unwrap().block_no, 1);
    }

    #[test]
    fn orphan_classification_pushes_re_intersect_and_clears_entries() {
        let mut s = fresh();
        install_validated_block(&mut s, 100, 1, 1, None);
        s.adopted_tip_hash = Some(h(1));

        let pid = PeerId(7);
        // Peer announces a block whose parent we've never heard of.
        let fx = s.on_tip_advanced(
            pid,
            pt(200, 99),
            5,
            5,
            h(99),
            200,
            Some(h(88)),
            &[0xAA; 4],
            Instant::now(),
        );
        assert!(fx
            .iter()
            .any(|e| matches!(e, PraosEffect::ReIntersect { peer_id } if *peer_id == pid)));
        // Entries cleared, peer placed on cooldown.
        assert!(s.peer_chains.get(&pid).unwrap().tip().is_none());
        assert!(s.orphan_cooldown.contains_key(&pid));
    }
}
