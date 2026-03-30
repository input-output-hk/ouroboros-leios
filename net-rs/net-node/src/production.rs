//! Block production via fake VRF lottery.
//!
//! Each slot, the producer runs a stake-weighted lottery to decide whether
//! to produce ranking blocks (Praos), input blocks, endorser blocks, and
//! votes (Leios). The lottery is ported from sim-rs.

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use net_core::types::{BlockBody, Point, WrappedHeader};

use crate::config::ProductionConfig;

/// A produced Leios endorser block.
pub struct ProducedEb {
    pub point: Point,
    pub data: Vec<u8>,
}

/// A produced Leios vote batch.
pub struct ProducedVotes {
    pub vote_ids: Vec<(u64, Vec<u8>)>,
    pub vote_data: Vec<Vec<u8>>,
}

/// Produces fake blocks based on a VRF lottery.
pub struct BlockProducer {
    rng: StdRng,
    stake: u64,
    total_stake: u64,
    config: ProductionConfig,
    block_count: u64,
    eb_count: u64,
    vote_count: u64,
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
            config: config.clone(),
            block_count: 0,
            eb_count: 0,
            vote_count: 0,
        }
    }

    /// Returns true if this node has any stake allocated for production.
    pub fn is_active(&self) -> bool {
        self.stake > 0 && self.total_stake > 0
    }

    /// Run the VRF lottery for a Praos ranking block at the given slot.
    pub fn try_produce_block(&mut self, slot: u64) -> Option<(Point, WrappedHeader, BlockBody)> {
        if !self.is_active() {
            return None;
        }

        if !self.run_lottery(self.config.rb_generation_probability) {
            return None;
        }

        self.block_count += 1;
        Some(self.make_fake_block(slot))
    }

    /// Try to produce a Leios endorser block. Called at stage boundaries.
    pub fn try_produce_eb(&mut self, slot: u64) -> Option<ProducedEb> {
        if !self.is_active() || self.config.eb_generation_probability <= 0.0 {
            return None;
        }

        if !self.run_lottery(self.config.eb_generation_probability) {
            return None;
        }

        self.eb_count += 1;

        let mut hash = [0u8; 32];
        self.rng.fill(&mut hash);
        let point = Point::Specific { slot, hash };
        let data = vec![0x82, slot as u8, 0x00]; // minimal CBOR

        Some(ProducedEb { point, data })
    }

    /// Try to produce Leios votes. Called at stage boundaries.
    pub fn try_produce_votes(&mut self, slot: u64) -> Option<ProducedVotes> {
        if !self.is_active() || self.config.vote_generation_probability <= 0.0 {
            return None;
        }

        if !self.run_lottery(self.config.vote_generation_probability) {
            return None;
        }

        let num_votes = self.rng.gen_range(1..=3u8);
        let mut vote_ids = Vec::new();
        let mut vote_data = Vec::new();
        for v in 0..num_votes {
            vote_ids.push((slot, vec![v]));
            vote_data.push(vec![0xA0, v]); // minimal CBOR
        }

        self.vote_count += num_votes as u64;

        Some(ProducedVotes {
            vote_ids,
            vote_data,
        })
    }

    /// Check if this slot is a stage boundary.
    pub fn is_stage_boundary(&self, slot: u64) -> bool {
        self.config.stage_length_slots > 0 && slot.is_multiple_of(self.config.stage_length_slots)
    }

    /// Number of Praos blocks produced so far.
    pub fn block_count(&self) -> u64 {
        self.block_count
    }

    /// Run the VRF lottery for a given success rate. Returns true on win.
    fn run_lottery(&mut self, probability: f64) -> bool {
        let target = compute_target_vrf_stake(self.stake, self.total_stake, probability);
        let roll: u64 = self.rng.gen_range(0..self.total_stake);
        roll < target
    }

    /// Build a fake block with minimal opaque CBOR.
    fn make_fake_block(&mut self, slot: u64) -> (Point, WrappedHeader, BlockBody) {
        let mut hash = [0u8; 32];
        self.rng.fill(&mut hash);

        let point = Point::Specific { slot, hash };

        let mut cbor_buf = Vec::new();
        let mut enc = minicbor::Encoder::new(&mut cbor_buf);
        // Encode as a 2-element array [slot, hash] for minimal structure.
        let _ = enc
            .array(2)
            .and_then(|e| e.u64(slot))
            .and_then(|e| e.bytes(&hash));
        let header = WrappedHeader::opaque(cbor_buf.clone());
        let body = BlockBody::opaque(cbor_buf);

        (point, header, body)
    }
}

/// Compute VRF target stake (ported from sim-rs lottery.rs).
fn compute_target_vrf_stake(stake: u64, total_stake: u64, success_rate: f64) -> u64 {
    let ratio = stake as f64 / total_stake as f64;
    (total_stake as f64 * ratio * success_rate) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    fn base_config() -> ProductionConfig {
        ProductionConfig {
            stake: 0,
            total_stake: 1000,
            ..Default::default()
        }
    }

    #[test]
    fn zero_stake_never_produces() {
        let config = base_config();
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
            rb_generation_probability: 1.0,
            ..base_config()
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
            rb_generation_probability: 0.5,
            ..base_config()
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
        assert!(!a.is_empty());
    }

    #[test]
    fn approximate_production_rate() {
        let config = ProductionConfig {
            stake: 100,
            rb_generation_probability: 0.5,
            ..base_config()
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
        assert_eq!(compute_target_vrf_stake(100, 1000, 1.0), 100);
        assert_eq!(compute_target_vrf_stake(500, 1000, 0.5), 250);
        assert_eq!(compute_target_vrf_stake(1000, 1000, 1.0), 1000);
        assert_eq!(compute_target_vrf_stake(0, 1000, 1.0), 0);
    }

    #[test]
    fn stage_boundary_detection() {
        let config = ProductionConfig {
            stage_length_slots: 20,
            ..base_config()
        };
        let producer = BlockProducer::new(&config, Some(42));
        assert!(producer.is_stage_boundary(0));
        assert!(producer.is_stage_boundary(20));
        assert!(producer.is_stage_boundary(40));
        assert!(!producer.is_stage_boundary(1));
        assert!(!producer.is_stage_boundary(19));
    }

    #[test]
    fn eb_production_at_full_stake() {
        let config = ProductionConfig {
            stake: 1000,
            eb_generation_probability: 1.0,
            ..base_config()
        };
        let mut producer = BlockProducer::new(&config, Some(42));
        let eb = producer.try_produce_eb(100);
        assert!(eb.is_some());
    }

    #[test]
    fn vote_production_at_full_stake() {
        let config = ProductionConfig {
            stake: 1000,
            vote_generation_probability: 1.0,
            ..base_config()
        };
        let mut producer = BlockProducer::new(&config, Some(42));
        let votes = producer.try_produce_votes(100);
        assert!(votes.is_some());
        let v = votes.unwrap();
        assert!(!v.vote_ids.is_empty());
        assert_eq!(v.vote_ids.len(), v.vote_data.len());
    }
}
