//! Weighted Fait Accompli (wFA) persistent committee allocation.
//!
//! Each node, at the same epoch boundary, runs the same deterministic
//! stake-weighted lottery to allocate `persistent_voters` seats among the
//! pools in the stake registry. Identical inputs → identical outputs, so
//! every node arrives at the same persistent committee without
//! communication.
//!
//! Algorithm: independent multinomial draws from the cumulative stake
//! distribution. A pool with stake `s` out of `T` total receives each seat
//! with probability `s/T`; expected total seats per pool ≈ `N_pv × s/T`.
//! High-stake pools may win multiple seats; zero-stake pools win none.

use std::collections::BTreeMap;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use crate::config::StakeEntry;

/// Allocate `persistent_voters` seats deterministically from the given
/// stake registry. Returns a map from `node_id` to seat count for each
/// pool that won at least one seat.
///
/// `seed` must be identical across all nodes in the network (e.g. derived
/// from genesis time and an epoch counter) so they produce the same
/// committee.
#[allow(dead_code)] // wired by the WFA+LS voting integration commit
pub fn allocate_persistent_seats(
    stake_registry: &[StakeEntry],
    persistent_voters: u32,
    seed: u64,
) -> BTreeMap<String, u32> {
    let total_stake: u128 = stake_registry.iter().map(|e| e.stake as u128).sum();
    if total_stake == 0 || persistent_voters == 0 || stake_registry.is_empty() {
        return BTreeMap::new();
    }

    // Cumulative stake array: cumsum[i] = sum of stakes 0..=i. Each seat
    // is awarded by drawing r in [0, total) and finding the first index
    // whose cumulative stake exceeds r.
    let mut cumsum: Vec<u128> = Vec::with_capacity(stake_registry.len());
    let mut running: u128 = 0;
    for entry in stake_registry {
        running += entry.stake as u128;
        cumsum.push(running);
    }

    let mut rng = StdRng::seed_from_u64(seed);
    let mut seats: BTreeMap<String, u32> = BTreeMap::new();
    for _ in 0..persistent_voters {
        let r: u128 = rng.gen_range(0..total_stake);
        // Binary search for the first cumsum > r.
        let idx = cumsum.partition_point(|&c| c <= r);
        let node_id = &stake_registry[idx].node_id;
        *seats.entry(node_id.clone()).or_insert(0) += 1;
    }
    seats
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(id: &str, stake: u64) -> StakeEntry {
        StakeEntry {
            node_id: id.to_string(),
            stake,
        }
    }

    #[test]
    fn deterministic_for_same_inputs() {
        let registry = vec![
            entry("node-0", 100),
            entry("node-1", 200),
            entry("node-2", 300),
        ];
        let a = allocate_persistent_seats(&registry, 50, 42);
        let b = allocate_persistent_seats(&registry, 50, 42);
        assert_eq!(a, b);
    }

    #[test]
    fn different_seed_gives_different_allocation() {
        let registry = vec![entry("node-0", 100), entry("node-1", 100)];
        let a = allocate_persistent_seats(&registry, 100, 1);
        let b = allocate_persistent_seats(&registry, 100, 2);
        // Counts differ for at least one node with very high probability.
        assert_ne!(a, b);
    }

    #[test]
    fn total_seats_equals_n_pv() {
        let registry = vec![
            entry("node-0", 100),
            entry("node-1", 200),
            entry("node-2", 0),
        ];
        let seats = allocate_persistent_seats(&registry, 480, 42);
        let total: u32 = seats.values().sum();
        assert_eq!(total, 480);
    }

    #[test]
    fn zero_stake_node_gets_no_seats() {
        let registry = vec![
            entry("relay-0", 0),
            entry("relay-1", 0),
            entry("pool-0", 1000),
        ];
        let seats = allocate_persistent_seats(&registry, 100, 7);
        assert!(!seats.contains_key("relay-0"));
        assert!(!seats.contains_key("relay-1"));
        assert_eq!(seats["pool-0"], 100);
    }

    #[test]
    fn allocation_is_stake_proportional() {
        // 100 nodes, geometric stakes: 1, 2, 4, ..., 2^99 — top node has
        // ~50% of total stake. With 1000 seats and seed 42, the top node
        // should win ≳ 400 seats (allowing PRNG variance).
        let registry: Vec<StakeEntry> = (0..20)
            .map(|i| entry(&format!("node-{i}"), 1u64 << i))
            .collect();
        let seats = allocate_persistent_seats(&registry, 1000, 42);
        let top_node_seats = seats.get("node-19").copied().unwrap_or(0);
        // node-19 has 2^19 / (2^20 - 1) ≈ 50% of stake; expect ~500 seats.
        assert!(
            (400..=600).contains(&top_node_seats),
            "top node seats={top_node_seats}, expected ~500"
        );
    }

    #[test]
    fn empty_registry_returns_empty() {
        let seats = allocate_persistent_seats(&[], 100, 42);
        assert!(seats.is_empty());
    }

    #[test]
    fn zero_seats_returns_empty() {
        let registry = vec![entry("node-0", 100)];
        let seats = allocate_persistent_seats(&registry, 0, 42);
        assert!(seats.is_empty());
    }

    #[test]
    fn all_zero_stake_returns_empty() {
        let registry = vec![entry("relay-0", 0), entry("relay-1", 0)];
        let seats = allocate_persistent_seats(&registry, 100, 42);
        assert!(seats.is_empty());
    }

    #[test]
    fn all_seats_to_only_pool() {
        let registry = vec![
            entry("relay", 0),
            entry("only-pool", 1000),
            entry("relay-2", 0),
        ];
        let seats = allocate_persistent_seats(&registry, 480, 42);
        assert_eq!(seats.len(), 1);
        assert_eq!(seats["only-pool"], 480);
    }
}
