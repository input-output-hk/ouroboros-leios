//! Behaviour registry — maps a serialisable spec to a concrete
//! [`Behaviour`] instance.
//!
//! Each consumer (sim-rs, net-node) deserialises a [`BehaviourSpec`]
//! from its config (TOML / JSON) and calls [`build`] to materialise
//! the trait object.  Adding a new behaviour: append a variant to
//! [`BehaviourSpec`] and a match arm in [`build`].
//!
//! [`Behaviour`]: super::Behaviour

use serde::{Deserialize, Serialize};

use super::behaviours::{LazyVoter, RbEquivocator};
use super::{Behaviour, CompositeBehaviour, HonestBehaviour};
use crate::leios::NoVoteReason;

/// Serialisable description of a node's behaviour.  Concrete behaviours
/// add variants here; each variant carries its own parameters.  The
/// `kind` field is the discriminant (`#[serde(tag = "kind")]`).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum BehaviourSpec {
    /// Default no-op.  Indistinguishable from no behaviour at all.
    Honest,
    /// Compose multiple behaviours.  Hooks dispatch in declaration
    /// order; first non-`Continue` wins.
    Composite { children: Vec<BehaviourSpec> },
    /// Per slot at which the local node would emit one RB, emit a
    /// duplicate carrying a different body hash (CIP-0164
    /// RB-header-equivocation adversary).  See
    /// [`super::behaviours::RbEquivocator`].
    RbEquivocator,
    /// Never casts a vote — always overrides the CIP-0164 voting
    /// predicate to abstain with `reason`.  Defaults to `WrongEB` (the
    /// most innocuous-looking abstention).
    #[serde(rename = "lazy-voter")]
    LazyVoter {
        #[serde(default = "default_lazy_reason")]
        reason: NoVoteReason,
    },
}

fn default_lazy_reason() -> NoVoteReason {
    NoVoteReason::WrongEB
}

impl Default for BehaviourSpec {
    fn default() -> Self {
        Self::Honest
    }
}

/// Materialise a [`BehaviourSpec`] into a boxed trait object.
pub fn build(spec: &BehaviourSpec) -> Box<dyn Behaviour> {
    match spec {
        BehaviourSpec::Honest => Box::new(HonestBehaviour),
        BehaviourSpec::Composite { children } => {
            let kids: Vec<Box<dyn Behaviour>> = children.iter().map(build).collect();
            Box::new(CompositeBehaviour::new(kids))
        }
        BehaviourSpec::RbEquivocator => Box::new(RbEquivocator::default()),
        BehaviourSpec::LazyVoter { reason } => Box::new(LazyVoter { reason: *reason }),
    }
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
            children: vec![BehaviourSpec::Honest, BehaviourSpec::RbEquivocator],
        };
        let json = serde_json::to_string(&spec).unwrap();
        let back: BehaviourSpec = serde_json::from_str(&json).unwrap();
        match back {
            BehaviourSpec::Composite { children } => {
                assert_eq!(children.len(), 2);
                assert!(matches!(children[0], BehaviourSpec::Honest));
                assert!(matches!(children[1], BehaviourSpec::RbEquivocator));
            }
            _ => panic!("expected Composite"),
        }
    }

    #[test]
    fn build_honest_has_name_honest() {
        let b = build(&BehaviourSpec::Honest);
        assert_eq!(b.name(), "honest");
    }

    #[test]
    fn build_composite_has_name_composite() {
        let b = build(&BehaviourSpec::Composite { children: vec![] });
        assert_eq!(b.name(), "composite");
    }
}
