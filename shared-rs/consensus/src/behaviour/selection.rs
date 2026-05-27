//! Behaviour selection — pick which nodes in a multi-node deployment
//! run a given [`BehaviourSpec`].
//!
//! Consumers (sim-rs, net-cluster) hold a list of `(spec, selection)`
//! pairs describing an experiment and ask this module to materialise
//! the per-node assignment.  The module is sans-IO: it takes a stake
//! vector indexed in node order and returns indices into that vector.
//!
//! All variants are deterministic for a given seed so re-runs land on
//! the same nodes.  Stake-aware variants (`StakeRandom`, `StakeOrdered`,
//! `StakeFraction`) ignore zero-stake nodes — under mainnet-shaped
//! topologies these are relays that don't vote and aren't meaningful
//! targets for behaviour assignment.
//!
//! [`BehaviourSpec`]: super::BehaviourSpec

use std::collections::{BTreeMap, BTreeSet};

use rand::prelude::*;
use serde::{Deserialize, Serialize};

use super::BehaviourSpec;

/// Which subset of nodes runs a configured behaviour.
///
/// Serialised as a tagged TOML/YAML table:
///
/// ```toml
/// [behaviour_selection]
/// kind = "stake-fraction"
/// fraction = 0.2
/// ```
///
/// All variants are deterministic for a given seed so re-runs land on
/// the same nodes.  Stake-aware variants ignore zero-stake nodes
/// (e.g. relays under `mainnet-shaped` topologies).
#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum BehaviourSelection {
    /// Attach the behaviour to every node.
    All,
    /// Attach the behaviour to a hand-listed set of node indices.
    Nodes {
        #[serde(default)]
        indices: Vec<usize>,
    },
    /// Pick `count` random nodes (deterministically, seeded) from those
    /// with `stake > 0`.  Useful for "this many adversaries somewhere
    /// in the voting set" without concentrating on the largest pools.
    StakeRandom { count: usize },
    /// Pick `count` nodes from those with `stake > 0`, ordered by stake
    /// descending and tie-broken by index ascending.  Targets the
    /// largest pools first.
    StakeOrdered { count: usize },
    /// Pick the smallest prefix of stake-bearing nodes (ordered by
    /// stake descending, tie-broken by index ascending) whose
    /// cumulative stake covers `fraction` of the total stake.  Same
    /// shape as CIP-0164 top-stake committee selection
    /// (`top_centile_of_stake`) — `fraction = 0.2` makes 20% of the
    /// *voting weight* run the behaviour, regardless of how many nodes
    /// that turns out to be.
    StakeFraction { fraction: f64 },
}

/// Resolve a [`BehaviourSelection`] to the concrete set of node
/// indices it picks.  `seed` is the deterministic RNG seed for
/// `StakeRandom`; the other variants ignore it.
pub fn resolve_selection(
    selection: &BehaviourSelection,
    stakes: &[u64],
    seed: Option<u64>,
) -> BTreeSet<usize> {
    match selection {
        BehaviourSelection::All => (0..stakes.len()).collect(),
        BehaviourSelection::Nodes { indices } => indices
            .iter()
            .copied()
            .filter(|&i| i < stakes.len())
            .collect(),
        BehaviourSelection::StakeOrdered { count } => {
            stake_ranked(stakes).into_iter().take(*count).collect()
        }
        BehaviourSelection::StakeRandom { count } => {
            let mut bearers: Vec<usize> = stakes
                .iter()
                .enumerate()
                .filter(|(_, &s)| s > 0)
                .map(|(i, _)| i)
                .collect();
            let mut rng = StdRng::seed_from_u64(seed.unwrap_or(0));
            bearers.shuffle(&mut rng);
            bearers.into_iter().take(*count).collect()
        }
        BehaviourSelection::StakeFraction { fraction } => {
            let total: u128 = stakes.iter().map(|&s| s as u128).sum();
            if total == 0 {
                return BTreeSet::new();
            }
            let f = fraction.clamp(0.0, 1.0);
            let target = (total as f64 * f).ceil() as u128;
            let mut chosen = BTreeSet::new();
            let mut acc: u128 = 0;
            for (idx, stake) in stake_ranked_with_stake(stakes) {
                if acc >= target {
                    break;
                }
                chosen.insert(idx);
                acc += stake as u128;
            }
            chosen
        }
    }
}

/// Resolve a list of `(spec, selection)` items to a per-node
/// [`BehaviourSpec`] assignment.
///
/// Items are walked in declaration order.  When two items select the
/// same node, the specs **compose** rather than override: the entry
/// becomes [`BehaviourSpec::Composite`] with the existing spec followed
/// by the new one.  This matches the documented composite-dispatch
/// semantics (first non-`Continue` wins) and the
/// [`build`](super::build) helper's seeding contract — children are
/// re-seeded via `child_seed(seed, idx)`, so a composed assignment
/// from this resolver behaves the same as a hand-written
/// [`BehaviourSpec::Composite`].
///
/// `seed` is salted per item via [`child_seed`](super::registry::child_seed),
/// so two `StakeRandom` items pick independent subsets rather than the
/// same shuffle (or nested prefixes when their `count` differs).
///
/// Nodes not picked by any item are absent from the returned map; the
/// caller treats those as honest.
pub fn resolve_specs(
    items: &[(BehaviourSpec, BehaviourSelection)],
    stakes: &[u64],
    seed: Option<u64>,
) -> BTreeMap<usize, BehaviourSpec> {
    let mut out: BTreeMap<usize, BehaviourSpec> = BTreeMap::new();
    for (item_idx, (spec, selection)) in items.iter().enumerate() {
        let item_seed = seed.map(|s| super::registry::child_seed(s, item_idx));
        let picked = resolve_selection(selection, stakes, item_seed);
        for idx in picked {
            match out.remove(&idx) {
                None => {
                    out.insert(idx, spec.clone());
                }
                Some(existing) => {
                    let composed = match existing {
                        BehaviourSpec::Composite { children: mut kids } => {
                            kids.push(spec.clone());
                            BehaviourSpec::Composite { children: kids }
                        }
                        other => BehaviourSpec::Composite {
                            children: vec![other, spec.clone()],
                        },
                    };
                    out.insert(idx, composed);
                }
            }
        }
    }
    out
}

/// Stake-bearing nodes sorted by stake descending, ties broken by
/// index ascending.  Returns indices only; pair with
/// [`stake_ranked_with_stake`] when you also need the stake.
fn stake_ranked(stakes: &[u64]) -> Vec<usize> {
    stake_ranked_with_stake(stakes)
        .into_iter()
        .map(|(i, _)| i)
        .collect()
}

fn stake_ranked_with_stake(stakes: &[u64]) -> Vec<(usize, u64)> {
    let mut ranked: Vec<(usize, u64)> = stakes
        .iter()
        .enumerate()
        .filter(|(_, &s)| s > 0)
        .map(|(i, &s)| (i, s))
        .collect();
    ranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    ranked
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_picks_every_node() {
        let set = resolve_selection(&BehaviourSelection::All, &[0, 5, 0, 5, 0], None);
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn nodes_verbatim() {
        let set = resolve_selection(
            &BehaviourSelection::Nodes {
                indices: vec![1, 3],
            },
            &[1, 1, 1, 1],
            None,
        );
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![1, 3]);
    }

    #[test]
    fn nodes_drops_out_of_range() {
        let set = resolve_selection(
            &BehaviourSelection::Nodes {
                indices: vec![0, 99, 2],
            },
            &[1, 1, 1],
            None,
        );
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![0, 2]);
    }

    #[test]
    fn stake_ordered_filters_zero_stake_and_takes_top_n() {
        let stakes = vec![10, 100, 50, 0, 200];
        let set =
            resolve_selection(&BehaviourSelection::StakeOrdered { count: 2 }, &stakes, None);
        // Sorted desc by stake: 4 (200), 1 (100), 2 (50), 0 (10); top 2 = {1, 4}.
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![1, 4]);
    }

    #[test]
    fn stake_ordered_count_zero_returns_empty() {
        let set = resolve_selection(
            &BehaviourSelection::StakeOrdered { count: 0 },
            &[10, 10, 10],
            None,
        );
        assert!(set.is_empty());
    }

    #[test]
    fn stake_ordered_count_exceeds_pool_takes_all_bearers() {
        let stakes = vec![10, 0, 20, 0, 30];
        let set = resolve_selection(
            &BehaviourSelection::StakeOrdered { count: 99 },
            &stakes,
            None,
        );
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![0, 2, 4]);
    }

    #[test]
    fn stake_random_is_deterministic_for_seed() {
        let stakes = vec![10, 0, 20, 0, 30, 0, 40, 0, 50];
        let mk = |seed: u64| -> BTreeSet<usize> {
            resolve_selection(&BehaviourSelection::StakeRandom { count: 2 }, &stakes, Some(seed))
        };
        assert_eq!(mk(42), mk(42));
        let a = mk(42);
        let b = mk(43);
        assert_ne!(a, b, "seed should change the selection");
        let bearers: BTreeSet<usize> = [0, 2, 4, 6, 8].into_iter().collect();
        for node in &a {
            assert!(bearers.contains(node));
        }
    }

    #[test]
    fn stake_random_count_zero_returns_empty() {
        let set = resolve_selection(
            &BehaviourSelection::StakeRandom { count: 0 },
            &[10, 20, 30],
            Some(0),
        );
        assert!(set.is_empty());
    }

    #[test]
    fn stake_fraction_picks_smallest_prefix_covering_target() {
        let stakes = vec![100, 100, 100, 100, 100];
        let set = resolve_selection(
            &BehaviourSelection::StakeFraction { fraction: 0.4 },
            &stakes,
            None,
        );
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![0, 1]);
    }

    #[test]
    fn stake_fraction_with_uneven_pools() {
        let stakes = vec![10, 100, 50, 200];
        let set = resolve_selection(
            &BehaviourSelection::StakeFraction { fraction: 0.5 },
            &stakes,
            None,
        );
        // 200 alone (idx 3) already covers 50% of 360 = 180.
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![3]);
    }

    #[test]
    fn stake_fraction_skips_relays() {
        let stakes = vec![100, 100, 100, 0, 0, 0, 0];
        let set = resolve_selection(
            &BehaviourSelection::StakeFraction { fraction: 0.3 },
            &stakes,
            None,
        );
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![0]);
    }

    #[test]
    fn stake_fraction_zero_returns_empty() {
        let set = resolve_selection(
            &BehaviourSelection::StakeFraction { fraction: 0.0 },
            &[100, 100],
            None,
        );
        assert!(set.is_empty());
    }

    #[test]
    fn stake_fraction_one_picks_all_bearers() {
        let stakes = vec![10, 0, 20, 0, 30];
        let set = resolve_selection(
            &BehaviourSelection::StakeFraction { fraction: 1.0 },
            &stakes,
            None,
        );
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![0, 2, 4]);
    }

    #[test]
    fn resolve_specs_empty_items_returns_empty() {
        let out = resolve_specs(&[], &[1, 1, 1], None);
        assert!(out.is_empty());
    }

    #[test]
    fn resolve_specs_disjoint_selections_produce_plain_specs() {
        let items = vec![
            (
                BehaviourSpec::LazyVoter {
                    reason: crate::leios::NoVoteReason::Declined,
                },
                BehaviourSelection::Nodes { indices: vec![0] },
            ),
            (
                BehaviourSpec::RbHeaderEquivocator { ways: 2 },
                BehaviourSelection::Nodes { indices: vec![1] },
            ),
        ];
        let out = resolve_specs(&items, &[1, 1, 1], None);
        assert!(matches!(out.get(&0), Some(BehaviourSpec::LazyVoter { .. })));
        assert!(matches!(
            out.get(&1),
            Some(BehaviourSpec::RbHeaderEquivocator { ways: 2 })
        ));
        assert!(out.get(&2).is_none());
    }

    #[test]
    fn resolve_specs_overlapping_selections_compose() {
        let items = vec![
            (
                BehaviourSpec::LazyVoter {
                    reason: crate::leios::NoVoteReason::Declined,
                },
                BehaviourSelection::All,
            ),
            (
                BehaviourSpec::RbHeaderEquivocator { ways: 2 },
                BehaviourSelection::Nodes { indices: vec![0] },
            ),
        ];
        let out = resolve_specs(&items, &[1, 1, 1], None);
        // Node 0: composed; nodes 1, 2: plain LazyVoter.
        match out.get(&0) {
            Some(BehaviourSpec::Composite { children }) => {
                assert_eq!(children.len(), 2);
                assert!(matches!(children[0], BehaviourSpec::LazyVoter { .. }));
                assert!(matches!(
                    children[1],
                    BehaviourSpec::RbHeaderEquivocator { ways: 2 }
                ));
            }
            other => panic!("expected Composite at node 0, got {:?}", other),
        }
        assert!(matches!(out.get(&1), Some(BehaviourSpec::LazyVoter { .. })));
        assert!(matches!(out.get(&2), Some(BehaviourSpec::LazyVoter { .. })));
    }

    #[test]
    fn resolve_specs_salts_seed_per_item_so_stake_random_items_are_independent() {
        // Two StakeRandom items with the same count would otherwise see
        // the same shuffle and pick the same nodes.  Per-item salting
        // via child_seed should give independent subsets.
        let stakes = vec![10, 20, 30, 40, 50, 60, 70, 80, 90, 100];
        let items = vec![
            (
                BehaviourSpec::LazyVoter {
                    reason: crate::leios::NoVoteReason::Declined,
                },
                BehaviourSelection::StakeRandom { count: 3 },
            ),
            (
                BehaviourSpec::RbHeaderEquivocator { ways: 2 },
                BehaviourSelection::StakeRandom { count: 3 },
            ),
        ];
        let out = resolve_specs(&items, &stakes, Some(7));
        let lazy: BTreeSet<usize> = out
            .iter()
            .filter_map(|(idx, spec)| match spec {
                BehaviourSpec::LazyVoter { .. } => Some(*idx),
                _ => None,
            })
            .collect();
        let equiv: BTreeSet<usize> = out
            .iter()
            .filter_map(|(idx, spec)| match spec {
                BehaviourSpec::RbHeaderEquivocator { .. } => Some(*idx),
                _ => None,
            })
            .collect();
        assert_ne!(
            lazy, equiv,
            "two StakeRandom items with same count should select different subsets"
        );
    }

    #[test]
    fn resolve_specs_three_way_overlap_appends_to_existing_composite() {
        // Three items, all selecting node 0 — composite should grow
        // linearly, not nest.
        let items = vec![
            (
                BehaviourSpec::LazyVoter {
                    reason: crate::leios::NoVoteReason::Declined,
                },
                BehaviourSelection::Nodes { indices: vec![0] },
            ),
            (
                BehaviourSpec::RbHeaderEquivocator { ways: 2 },
                BehaviourSelection::Nodes { indices: vec![0] },
            ),
            (BehaviourSpec::Honest, BehaviourSelection::Nodes { indices: vec![0] }),
        ];
        let out = resolve_specs(&items, &[1], None);
        match out.get(&0) {
            Some(BehaviourSpec::Composite { children }) => {
                assert_eq!(children.len(), 3);
            }
            other => panic!("expected Composite with 3 children, got {:?}", other),
        }
    }
}
