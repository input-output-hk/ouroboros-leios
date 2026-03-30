//! Block production via fake VRF lottery.
//!
//! Each slot, the producer runs a stake-weighted lottery to decide whether
//! to produce a ranking block. The lottery is ported from sim-rs.

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use net_core::types::{BlockBody, Point, WrappedHeader};

use crate::config::ProductionConfig;

/// Produces fake blocks based on a VRF lottery.
pub struct BlockProducer {
    rng: StdRng,
    stake: u64,
    total_stake: u64,
    rb_probability: f64,
    block_count: u64,
}

impl BlockProducer {
    /// Create a new producer. If `seed` is None, uses entropy.
    pub fn new(config: &ProductionConfig, seed: Option<u64>) -> Self {
        let rng = match seed {
            Some(s) => StdRng::seed_from_u64(s),
            None => StdRng::from_entropy(),
        };
        Self {
            rng,
            stake: config.stake,
            total_stake: config.total_stake,
            rb_probability: config.rb_generation_probability,
            block_count: 0,
        }
    }

    /// Returns true if this node has any stake allocated for production.
    pub fn is_active(&self) -> bool {
        self.stake > 0 && self.total_stake > 0
    }

    /// Run the VRF lottery for the given slot. Returns the block triple
    /// (point, header, body) if the lottery wins, None otherwise.
    pub fn try_produce_block(&mut self, slot: u64) -> Option<(Point, WrappedHeader, BlockBody)> {
        if !self.is_active() {
            return None;
        }

        let target = compute_target_vrf_stake(self.stake, self.total_stake, self.rb_probability);
        let roll: u64 = self.rng.gen_range(0..self.total_stake);

        if roll >= target {
            return None;
        }

        self.block_count += 1;

        let mut hash = [0u8; 32];
        self.rng.fill(&mut hash);

        let point = Point::Specific { slot, hash };

        // Build minimal opaque CBOR (same approach as serve.rs).
        let mut cbor_buf = Vec::new();
        let mut enc = minicbor::Encoder::new(&mut cbor_buf);
        // Encode as a 2-element array [slot, hash] for minimal structure.
        if enc
            .array(2)
            .and_then(|e| e.u64(slot))
            .and_then(|e| e.bytes(&hash))
            .is_err()
        {
            return None;
        }
        let header = WrappedHeader::opaque(cbor_buf.clone());
        let body = BlockBody::opaque(cbor_buf);

        Some((point, header, body))
    }

    /// Number of blocks produced so far.
    pub fn block_count(&self) -> u64 {
        self.block_count
    }
}

/// Compute VRF target stake (ported from sim-rs lottery.rs).
///
/// Returns the threshold below which a random draw in `[0, total_stake)`
/// counts as a win.
fn compute_target_vrf_stake(stake: u64, total_stake: u64, success_rate: f64) -> u64 {
    let ratio = stake as f64 / total_stake as f64;
    (total_stake as f64 * ratio * success_rate) as u64
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::ProductionConfig;

    #[test]
    fn zero_stake_never_produces() {
        let config = ProductionConfig {
            stake: 0,
            total_stake: 1000,
            rb_generation_probability: 1.0,
        };
        let mut producer = BlockProducer::new(&config, Some(42));
        assert!(!producer.is_active());
        for slot in 0..100 {
            assert!(producer.try_produce_block(slot).is_none());
        }
    }

    #[test]
    fn full_stake_always_produces() {
        let config = ProductionConfig {
            stake: 1000,
            total_stake: 1000,
            rb_generation_probability: 1.0,
        };
        let mut producer = BlockProducer::new(&config, Some(42));
        assert!(producer.is_active());
        for slot in 0..100 {
            let result = producer.try_produce_block(slot);
            assert!(result.is_some(), "should produce at slot {slot}");
            let (point, _, _) = result.unwrap();
            match point {
                Point::Specific { slot: s, .. } => assert_eq!(s, slot),
                _ => panic!("expected Specific point"),
            }
        }
        assert_eq!(producer.block_count(), 100);
    }

    #[test]
    fn deterministic_with_same_seed() {
        let config = ProductionConfig {
            stake: 100,
            total_stake: 1000,
            rb_generation_probability: 0.5,
        };

        let run = |seed| {
            let mut producer = BlockProducer::new(&config, Some(seed));
            (0..1000)
                .filter_map(|slot| producer.try_produce_block(slot).map(|_| slot))
                .collect::<Vec<_>>()
        };

        let a = run(123);
        let b = run(123);
        assert_eq!(a, b);
        // With 5% expected rate (stake/total * probability = 0.1 * 0.5 = 0.05),
        // should produce roughly 50 blocks in 1000 slots.
        assert!(!a.is_empty());
    }

    #[test]
    fn approximate_production_rate() {
        let config = ProductionConfig {
            stake: 100,
            total_stake: 1000,
            rb_generation_probability: 0.5,
        };
        let mut producer = BlockProducer::new(&config, Some(99));
        let wins: usize = (0..10_000)
            .filter(|slot| producer.try_produce_block(*slot).is_some())
            .count();
        // Expected: 10000 * (100/1000) * 0.5 = 500, allow ±20%.
        assert!(
            (400..=600).contains(&wins),
            "wins={wins}, expected ~500 (5%)"
        );
    }

    #[test]
    fn vrf_target_computation() {
        // target = total_stake * (stake/total_stake) * success_rate
        //        = stake * success_rate  (when expanded)
        assert_eq!(compute_target_vrf_stake(100, 1000, 1.0), 100); // 100 * 1.0 = 100 (but divided over 1000 range -> 10% chance)
        assert_eq!(compute_target_vrf_stake(500, 1000, 0.5), 250); // 500 * 0.5
        assert_eq!(compute_target_vrf_stake(1000, 1000, 1.0), 1000);
        assert_eq!(compute_target_vrf_stake(0, 1000, 1.0), 0);
    }
}
