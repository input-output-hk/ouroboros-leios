//! Block production via fake VRF lottery.
//!
//! Each slot, the producer runs a stake-weighted lottery to decide whether
//! to produce ranking blocks (Praos), endorser blocks, and
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
    /// `prev_hash` is the hash of the parent block (from consensus tip).
    /// `block_number` is the chain height (parent block_number + 1).
    pub fn try_produce_block(
        &mut self,
        slot: u64,
        prev_hash: Option<[u8; 32]>,
        block_number: u64,
    ) -> Option<(Point, WrappedHeader, BlockBody)> {
        if !self.is_active() {
            return None;
        }

        if !self.run_lottery(self.config.rb_generation_probability) {
            return None;
        }

        self.block_count += 1;
        Some(self.make_fake_block(slot, prev_hash, block_number))
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

    /// Build a fake block with valid Shelley+ CBOR structure.
    ///
    /// The header and block body use proper era-tagged encoding so that
    /// `body.point()` and `WrappedHeader::parse()` both work correctly.
    /// The point hash uses `header_hash()`, matching the real
    /// Cardano derivation.
    fn make_fake_block(
        &mut self,
        slot: u64,
        prev_hash: Option<[u8; 32]>,
        block_number: u64,
    ) -> (Point, WrappedHeader, BlockBody) {
        let mut issuer_vkey = [0u8; 32];
        self.rng.fill(&mut issuer_vkey);
        let mut body_hash = [0u8; 32];
        self.rng.fill(&mut body_hash);

        // Build header_body: 10-field array (Shelley+ minimum).
        // [block_number, slot, prev_hash, issuer_vkey, vrf_vkey, vrf_result,
        //  body_size, block_body_hash, operational_cert, protocol_version]
        let mut header_body = Vec::new();
        let mut hb = minicbor::Encoder::new(&mut header_body);
        let _ = hb
            .array(10)
            .and_then(|e| e.u64(block_number)) // block_number
            .and_then(|e| e.u64(slot)) // slot
            .and_then(|e| match prev_hash {
                Some(h) => e.bytes(&h),
                None => e.null(),
            }) // prev_hash
            .and_then(|e| e.bytes(&issuer_vkey)) // issuer_vkey
            .and_then(|e| e.bytes(&[0u8; 32])) // vrf_vkey (placeholder)
            .and_then(|e| e.array(2)) // vrf_result: [output, proof]
            .and_then(|e| e.bytes(&[0u8; 32]))
            .and_then(|e| e.bytes(&[0u8; 64]))
            .and_then(|e| e.u32(0)) // body_size
            .and_then(|e| e.bytes(&body_hash)) // block_body_hash
            .and_then(|e| e.array(4)) // operational_cert: [vkey, counter, kes_period, sig]
            .and_then(|e| e.bytes(&[0u8; 32]))
            .and_then(|e| e.u64(0))
            .and_then(|e| e.u64(0))
            .and_then(|e| e.bytes(&[0u8; 64]))
            .and_then(|e| e.array(2)) // protocol_version: [major, minor]
            .and_then(|e| e.u32(10))
            .and_then(|e| e.u32(0));

        // Inner header: [header_body, body_signature]
        let mut header_inner = Vec::new();
        let mut hi = minicbor::Encoder::new(&mut header_inner);
        let _ = hi.array(2);
        header_inner.extend_from_slice(&header_body);
        let _ = minicbor::Encoder::new(&mut header_inner).bytes(&[0u8; 64]); // signature placeholder

        // Header CBOR: [era_tag, #6.24(header_inner)]
        let era: u32 = 7; // Conway
        let mut header_cbor = Vec::new();
        let mut he = minicbor::Encoder::new(&mut header_cbor);
        let _ = he
            .array(2)
            .and_then(|e| e.u32(era))
            .and_then(|e| e.tag(minicbor::data::Tag::new(24)))
            .and_then(|e| e.bytes(&header_inner));

        // Point: (slot, header_hash(header_cbor))
        let header = WrappedHeader::new(header_cbor.clone());
        let point = header
            .point()
            .expect("freshly-built Shelley+ header must parse");

        // Block body: #6.24([era_tag, [header, tx_bodies, tx_witnesses, metadata]])
        // The header inside the block must be the same bytes so body.point()
        // extracts the same hash.
        let mut block_inner = Vec::new();
        let mut bi = minicbor::Encoder::new(&mut block_inner);
        let _ = bi.array(2).and_then(|e| e.u32(era));
        // era_block: [header, tx_bodies, ...]
        let _ = minicbor::Encoder::new(&mut block_inner).array(4);
        // header: [header_body, sig] (raw, no #6.24 wrapping — matches real Cardano blocks)
        block_inner.extend_from_slice(&header_inner);
        // tx_bodies (empty map)
        let _ = minicbor::Encoder::new(&mut block_inner).map(0);
        // tx_witnesses (empty map)
        let _ = minicbor::Encoder::new(&mut block_inner).map(0);
        // metadata (null)
        let _ = minicbor::Encoder::new(&mut block_inner).null();

        let mut body_cbor = Vec::new();
        let _ = minicbor::Encoder::new(&mut body_cbor)
            .tag(minicbor::data::Tag::new(24))
            .and_then(|e| e.bytes(&block_inner));
        let body = BlockBody::new(body_cbor);

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
            assert!(producer.try_produce_block(slot, None, slot + 1).is_none());
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
            let result = producer.try_produce_block(slot, None, slot + 1);
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
                .filter_map(|slot| {
                    producer
                        .try_produce_block(slot, None, slot + 1)
                        .map(|_| slot)
                })
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
            .filter(|slot| producer.try_produce_block(*slot, None, 1).is_some())
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

    #[test]
    fn fake_block_has_parseable_cbor() {
        let config = ProductionConfig {
            stake: 1000,
            rb_generation_probability: 1.0,
            ..base_config()
        };
        let mut producer = BlockProducer::new(&config, Some(42));
        let (point, header, body) = producer.try_produce_block(12345, None, 1).unwrap();

        // Header should be parseable.
        assert!(header.parsed.is_some(), "header should parse");
        let info = header.parsed.as_ref().unwrap();
        assert_eq!(info.slot, 12345);
        assert_eq!(info.era, 7); // Conway

        // Header point should match the produced point.
        let header_point = header.point();
        assert!(header_point.is_some(), "header.point() should work");
        assert_eq!(header_point.unwrap(), point);

        // Block body should derive the same point.
        let body_point = body.point();
        assert!(body_point.is_some(), "body.point() should work");
        assert_eq!(body_point.unwrap(), point);

        // Body should also extract a parseable header.
        let extracted = body.header();
        assert!(extracted.is_some(), "body.header() should work");
        let ex = extracted.unwrap();
        assert!(ex.parsed.is_some());
        assert_eq!(ex.parsed.as_ref().unwrap().slot, 12345);
    }
}
