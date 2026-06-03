//! Behaviour registry — maps a serialisable spec to a concrete
//! [`Behaviour`] instance.
//!
//! Each consumer (sim-rs, net-node) deserialises a [`BehaviourSpec`]
//! from its config (TOML / JSON) and calls [`build`] to materialise
//! the trait object.  Adding a new behaviour: append a variant to
//! [`BehaviourSpec`] and a match arm in [`build`].
//!
//! `build` takes a `u64` seed alongside the spec — adversarial
//! behaviours that make per-peer or per-slot random choices (e.g. peer
//! partitioning for equivocation) seed their own deterministic RNG
//! from it.  Behaviours that don't use randomness ignore the seed.
//! Compositions hash `(seed, child_index)` to give each child its own
//! distinct deterministic stream.
//!
//! [`Behaviour`]: super::Behaviour

use serde::{Deserialize, Serialize};

use super::behaviours::{DeepReorg, LazyVoter, RbHeaderEquivocator, T22ThreatBehaviour};
use super::{Behaviour, CompositeBehaviour, HonestBehaviour};
use crate::leios::NoVoteReason;

/// Serialisable description of a node's behaviour.  Concrete behaviours
/// add variants here; each variant carries its own parameters.  The
/// `kind` field is the discriminant (`#[serde(tag = "kind")]`).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum BehaviourSpec {
    /// Default no-op.  Indistinguishable from no behaviour at all.
    #[default]
    Honest,
    /// Compose multiple behaviours.  Hooks dispatch in declaration
    /// order; first non-`Continue` wins.
    Composite { children: Vec<BehaviourSpec> },
    /// Praos-layer attack: every slot this node wins the RB lottery,
    /// produce `ways` distinct Ranking Blocks sharing
    /// `(slot, issuer)` and route each to a deterministic peer-id
    /// subset (CIP-0164 RB-header equivocation).  `ways >= 2`
    /// (1 degenerates to honest); the default is 2.  See
    /// [`super::behaviours::RbHeaderEquivocator`].
    #[serde(rename = "rb-header-equivocator")]
    RbHeaderEquivocator {
        #[serde(default = "default_equivocator_ways")]
        ways: u8,
    },
    /// Never casts a vote — always overrides the CIP-0164 voting
    /// predicate to abstain with `reason`.  Defaults to `Declined` so
    /// the abstention is visible in telemetry as policy abstention,
    /// not an honest predicate failure.
    #[serde(rename = "lazy-voter")]
    LazyVoter {
        #[serde(default = "default_lazy_reason")]
        reason: NoVoteReason,
    },
    /// T22 threat prototype. Filters EB/TX processing using deterministic
    /// checksum threshold policy.
    #[serde(rename = "t22")]
    T22 {
        vote_threshold: u8,
        non_voting_threshold: u8,
        hide_eb_tx_received: bool,
    },
    /// Producer-side chain chaos: every `every_slots` slots, roll this
    /// node's adopted chain back `depth` blocks and fork, so downstream
    /// followers must recover from a deep rollback that orphans their
    /// adopted tip.  See [`super::behaviours::DeepReorg`].
    #[serde(rename = "deep-reorg")]
    DeepReorg { every_slots: u64, depth: u64 },
}

fn default_lazy_reason() -> NoVoteReason {
    NoVoteReason::Declined
}

fn default_equivocator_ways() -> u8 {
    2
}

/// Materialise a [`BehaviourSpec`] into a shared
/// [`BehaviourHandle`](super::BehaviourHandle) — a single trait object
/// wrapped in `Arc<Mutex<Box<_>>>` and ready to install on multiple
/// states.  Caller clones the handle for each holder; later
/// `swap_handle` replaces the inner trait object atomically so every
/// holder observes the new behaviour.
pub fn build_handle(spec: &BehaviourSpec, seed: u64) -> super::BehaviourHandle {
    std::sync::Arc::new(std::sync::Mutex::new(build(spec, seed)))
}

/// Replace the trait object inside an existing
/// [`BehaviourHandle`](super::BehaviourHandle).  Used at runtime to
/// swap the live behaviour without invalidating any of the Arc clones
/// already distributed to the wrappers.
pub fn swap_handle(handle: &super::BehaviourHandle, spec: &BehaviourSpec, seed: u64) {
    *handle.lock().expect("behaviour mutex poisoned") = build(spec, seed);
}

/// Materialise a [`BehaviourSpec`] into a boxed trait object.
///
/// `seed` is the deterministic seed for behaviours that make random
/// choices (peer partitioning, lottery skipping, …).  Pass a per-node
/// value — e.g. a hash of the node identifier, or a config-supplied
/// integer.  Behaviours that don't need randomness ignore it.
pub fn build(spec: &BehaviourSpec, seed: u64) -> Box<dyn Behaviour> {
    match spec {
        BehaviourSpec::Honest => Box::new(HonestBehaviour),
        BehaviourSpec::Composite { children } => {
            let kids: Vec<Box<dyn Behaviour>> = children
                .iter()
                .enumerate()
                .map(|(i, c)| build(c, child_seed(seed, i)))
                .collect();
            Box::new(CompositeBehaviour::new(kids))
        }
        BehaviourSpec::RbHeaderEquivocator { ways } => {
            Box::new(RbHeaderEquivocator::new(*ways, seed))
        }
        BehaviourSpec::LazyVoter { reason } => Box::new(LazyVoter { reason: *reason }),
        BehaviourSpec::T22 {
            vote_threshold,
            non_voting_threshold,
            hide_eb_tx_received,
        } => Box::new(T22ThreatBehaviour::new(*vote_threshold, *non_voting_threshold, *hide_eb_tx_received)),
        BehaviourSpec::DeepReorg { every_slots, depth } => {
            Box::new(DeepReorg::new(*every_slots, *depth))
        }
    }
}

/// Mix `seed` with `child_index` to give each composite child a
/// distinct deterministic stream.  Uses Blake2b to avoid linear
/// correlations between sibling seeds.
pub(crate) fn child_seed(seed: u64, idx: usize) -> u64 {
    let mut h = blake2b_simd::Params::new().hash_length(8).to_state();
    h.update(&seed.to_le_bytes());
    h.update(&(idx as u64).to_le_bytes());
    let out = h.finalize();
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&out.as_bytes()[..8]);
    u64::from_le_bytes(buf)
}

/// Derive a deterministic u64 seed from a node identifier string.  Use
/// when the per-node config supplies no explicit RNG seed but the
/// behaviour still needs a stable starting point across re-runs.
pub fn seed_from_node_id(node_id: &str) -> u64 {
    let mut h = blake2b_simd::Params::new().hash_length(8).to_state();
    h.update(node_id.as_bytes());
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&h.finalize().as_bytes()[..8]);
    u64::from_le_bytes(buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn honest_round_trips() {
        let spec = BehaviourSpec::Honest;
        let json = serde_json::to_string(&spec).unwrap();
        let back: BehaviourSpec = serde_json::from_str(&json).unwrap();
        assert!(matches!(back, BehaviourSpec::Honest));
    }

    #[test]
    fn composite_round_trips() {
        let spec = BehaviourSpec::Composite {
            children: vec![
                BehaviourSpec::Honest,
                BehaviourSpec::RbHeaderEquivocator { ways: 2 },
                BehaviourSpec::T22 {
                    vote_threshold: 42,
                    non_voting_threshold: 99,
                    hide_eb_tx_received: false,
                },
            ],
        };
        let json = serde_json::to_string(&spec).unwrap();
        let back: BehaviourSpec = serde_json::from_str(&json).unwrap();
        match back {
            BehaviourSpec::Composite { children } => {
                assert_eq!(children.len(), 3);
                assert!(matches!(children[0], BehaviourSpec::Honest));
                assert!(matches!(children[1], BehaviourSpec::RbHeaderEquivocator { ways: 2 }));
                assert!(matches!(
                    children[2],
                    BehaviourSpec::T22 {
                        vote_threshold: 42,
                        non_voting_threshold: 99,
                        hide_eb_tx_received: false
                    }
                ));
            }
            _ => panic!("expected Composite"),
        }
    }

    #[test]
    fn build_honest_has_name_honest() {
        let b = build(&BehaviourSpec::Honest, 0);
        assert_eq!(b.name(), "honest");
    }

    #[test]
    fn build_composite_has_name_composite() {
        let b = build(&BehaviourSpec::Composite { children: vec![] }, 0);
        assert_eq!(b.name(), "composite");
    }

    #[test]
    fn child_seed_distinct_per_index() {
        let s = 0xCAFEBABE;
        let a = child_seed(s, 0);
        let b = child_seed(s, 1);
        let c = child_seed(s, 2);
        assert_ne!(a, b);
        assert_ne!(b, c);
        assert_ne!(a, c);
    }

    #[test]
    fn child_seed_deterministic() {
        let s = 0xC0FFEE;
        assert_eq!(child_seed(s, 7), child_seed(s, 7));
    }
}
