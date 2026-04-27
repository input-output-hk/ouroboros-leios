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

use crate::config::{CommitteeSelection, StakeEntry};

/// Allocate `persistent_voters` seats deterministically from the given
/// stake registry. Returns a map from `node_id` to seat count for each
/// pool that won at least one seat.
///
/// `seed` must be identical across all nodes in the network (e.g. derived
/// from genesis time and an epoch counter) so they produce the same
/// committee.
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

/// Build the persistent committee for any committee-selection mode.
///
/// - `WfaLs`: stake-weighted lottery for `persistent_voters` seats.
/// - `EveryoneVotes`: every pool with non-zero stake gets one seat.
/// - `StakeCentile`: pools whose cumulative stake (sorted descending)
///   covers the top `top_centile_of_stake` of total stake each get one
///   seat.
pub fn build_committee(
    selection: &CommitteeSelection,
    stake_registry: &[StakeEntry],
    seed: u64,
) -> BTreeMap<String, u32> {
    match selection {
        CommitteeSelection::WfaLs {
            persistent_voters, ..
        } => allocate_persistent_seats(stake_registry, *persistent_voters, seed),
        CommitteeSelection::EveryoneVotes => stake_registry
            .iter()
            .filter(|e| e.stake > 0)
            .map(|e| (e.node_id.clone(), 1u32))
            .collect(),
        CommitteeSelection::StakeCentile {
            top_centile_of_stake,
        } => top_centile_committee(stake_registry, *top_centile_of_stake),
    }
}

fn top_centile_committee(
    stake_registry: &[StakeEntry],
    top_centile_of_stake: f64,
) -> BTreeMap<String, u32> {
    let total_stake: u128 = stake_registry.iter().map(|e| e.stake as u128).sum();
    if total_stake == 0 {
        return BTreeMap::new();
    }
    let cutoff = (top_centile_of_stake.clamp(0.0, 1.0) * total_stake as f64) as u128;
    let mut sorted: Vec<&StakeEntry> = stake_registry.iter().filter(|e| e.stake > 0).collect();
    sorted.sort_by(|a, b| {
        b.stake
            .cmp(&a.stake)
            .then_with(|| a.node_id.cmp(&b.node_id))
    });
    let mut committee = BTreeMap::new();
    let mut running: u128 = 0;
    for entry in sorted {
        if running >= cutoff {
            break;
        }
        committee.insert(entry.node_id.clone(), 1u32);
        running += entry.stake as u128;
    }
    committee
}

/// Total expected vote weight per EB across the network. Used as the
/// denominator for the quorum threshold: `Σ weight ≥ q × this`.
pub fn expected_committee_size(
    selection: &CommitteeSelection,
    committee: &BTreeMap<String, u32>,
) -> u32 {
    let pv: u32 = committee.values().sum();
    let npv = match selection {
        CommitteeSelection::WfaLs {
            non_persistent_voters,
            ..
        } => *non_persistent_voters,
        _ => 0,
    };
    pv + npv
}

/// Construct the deterministic NPV eligibility signature for a given
/// pool and EB. Models a CIP-0164 VRF output: 48 bytes derived from
/// `(voter_id, eb_hash, eb_slot)` via Blake2b. In real Cardano this
/// would be a BLS signature requiring the pool's secret key; here it's
/// reproducible by anyone given the same inputs (we don't model BLS).
pub fn npv_eligibility_signature(voter_id: &[u8], eb_hash: &[u8; 32], eb_slot: u64) -> Vec<u8> {
    let mut hasher = blake2b_simd::Params::new().hash_length(48).to_state();
    hasher.update(b"net-rs/leios/npv-vrf");
    hasher.update(voter_id);
    hasher.update(eb_hash);
    hasher.update(&eb_slot.to_le_bytes());
    hasher.finalize().as_bytes().to_vec()
}

/// Re-run the NPV lottery from an eligibility signature and the pool's
/// stake to count wins. Both prover and verifier compute the same
/// count without it being transmitted on the wire — mirrors how a
/// CIP-0164 verifier reconstructs the lottery outcome from the VRF
/// proof and the pool's ledger-resolved stake.
pub fn count_npv_wins(
    signature: &[u8],
    stake: u64,
    total_stake: u64,
    non_persistent_voters: u32,
) -> u32 {
    if stake == 0 || total_stake == 0 || non_persistent_voters == 0 || signature.len() < 32 {
        return 0;
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&signature[..32]);
    let mut rng = StdRng::from_seed(seed);
    let p = stake as f64 / total_stake as f64;
    let mut wins: u32 = 0;
    for _ in 0..non_persistent_voters {
        if rng.gen::<f64>() < p {
            wins += 1;
        }
    }
    wins
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

    // -- build_committee ----------------------------------------------------

    #[test]
    fn build_committee_wfa_ls_uses_lottery() {
        let registry = vec![
            entry("relay", 0),
            entry("pool-a", 500),
            entry("pool-b", 500),
        ];
        let selection = CommitteeSelection::WfaLs {
            persistent_voters: 200,
            non_persistent_voters: 50,
        };
        let committee = build_committee(&selection, &registry, 42);
        assert!(!committee.contains_key("relay"));
        assert_eq!(committee.values().sum::<u32>(), 200);
    }

    #[test]
    fn build_committee_everyone_unit_seats() {
        let registry = vec![
            entry("relay", 0),
            entry("pool-a", 500),
            entry("pool-b", 500),
        ];
        let committee = build_committee(&CommitteeSelection::EveryoneVotes, &registry, 0);
        assert_eq!(committee.len(), 2);
        assert_eq!(committee["pool-a"], 1);
        assert_eq!(committee["pool-b"], 1);
        assert!(!committee.contains_key("relay"));
    }

    #[test]
    fn build_committee_centile_picks_top_pools() {
        // Stakes: 100, 80, 60, 40, 20 → total 300. Top 50% = 150.
        // Sorted: 100 (running 100), 80 (running 180) — stops there.
        let registry = vec![
            entry("a", 100),
            entry("b", 80),
            entry("c", 60),
            entry("d", 40),
            entry("e", 20),
        ];
        let selection = CommitteeSelection::StakeCentile {
            top_centile_of_stake: 0.5,
        };
        let committee = build_committee(&selection, &registry, 0);
        assert_eq!(committee.len(), 2);
        assert!(committee.contains_key("a"));
        assert!(committee.contains_key("b"));
    }

    #[test]
    fn build_committee_centile_full_includes_all_pools() {
        let registry = vec![
            entry("relay", 0),
            entry("pool-a", 100),
            entry("pool-b", 100),
        ];
        let selection = CommitteeSelection::StakeCentile {
            top_centile_of_stake: 1.0,
        };
        let committee = build_committee(&selection, &registry, 0);
        assert_eq!(committee.len(), 2);
        assert!(!committee.contains_key("relay"));
    }

    // -- expected_committee_size --------------------------------------------

    #[test]
    fn expected_size_wfa_ls_is_pv_plus_npv() {
        let selection = CommitteeSelection::WfaLs {
            persistent_voters: 480,
            non_persistent_voters: 120,
        };
        let mut committee = BTreeMap::new();
        committee.insert("a".to_string(), 480u32);
        assert_eq!(expected_committee_size(&selection, &committee), 600);
    }

    #[test]
    fn expected_size_everyone_no_npv() {
        let mut committee = BTreeMap::new();
        committee.insert("a".to_string(), 1);
        committee.insert("b".to_string(), 1);
        assert_eq!(
            expected_committee_size(&CommitteeSelection::EveryoneVotes, &committee),
            2
        );
    }

    // -- NPV eligibility ----------------------------------------------------

    #[test]
    fn npv_signature_deterministic() {
        let eb_hash = [0xAB; 32];
        let a = npv_eligibility_signature(b"node-0", &eb_hash, 100);
        let b = npv_eligibility_signature(b"node-0", &eb_hash, 100);
        assert_eq!(a, b);
        assert_eq!(a.len(), 48);
    }

    #[test]
    fn npv_signature_differs_per_voter_or_eb() {
        let eb_hash = [0xAB; 32];
        let a = npv_eligibility_signature(b"node-0", &eb_hash, 100);
        let b = npv_eligibility_signature(b"node-1", &eb_hash, 100);
        let c = npv_eligibility_signature(b"node-0", &[0xCD; 32], 100);
        let d = npv_eligibility_signature(b"node-0", &eb_hash, 101);
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(a, d);
    }

    #[test]
    fn npv_count_zero_stake_is_zero() {
        let sig = npv_eligibility_signature(b"node-0", &[0; 32], 1);
        assert_eq!(count_npv_wins(&sig, 0, 1000, 100), 0);
    }

    #[test]
    fn npv_count_reproducible() {
        let sig = npv_eligibility_signature(b"node-0", &[0; 32], 1);
        let a = count_npv_wins(&sig, 40, 1000, 120);
        let b = count_npv_wins(&sig, 40, 1000, 120);
        assert_eq!(a, b);
    }

    #[test]
    fn npv_count_bigger_pool_more_wins() {
        // Mean over many distinct EBs.
        let big: u64 = (0..200)
            .map(|slot| {
                let sig = npv_eligibility_signature(b"big", &[0; 32], slot);
                count_npv_wins(&sig, 400, 1000, 120) as u64
            })
            .sum();
        let small: u64 = (0..200)
            .map(|slot| {
                let sig = npv_eligibility_signature(b"small", &[0; 32], slot);
                count_npv_wins(&sig, 40, 1000, 120) as u64
            })
            .sum();
        // Expected: big ≈ 200×120×0.4 = 9600; small ≈ 960. Ratio ~10×.
        assert!(big as f64 / small as f64 > 5.0);
    }
}
