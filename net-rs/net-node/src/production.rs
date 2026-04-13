//! Block production via fake VRF lottery.
//!
//! Each slot, the producer runs a stake-weighted lottery to decide whether
//! to produce ranking blocks (Praos), endorser blocks, and
//! votes (Leios). The lottery is ported from sim-rs.

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tokio::sync::watch;

use net_core::types::{BlockBody, Point, WrappedHeader};

use crate::config::{DynamicConfig, ProductionConfig};

/// A produced Leios endorser block.
pub struct ProducedEb {
    pub point: Point,
    pub data: Vec<u8>,
}

/// A produced Leios vote batch.
#[allow(dead_code)]
pub struct ProducedVotes {
    pub vote_ids: Vec<(u64, Vec<u8>)>,
    pub vote_data: Vec<Vec<u8>>,
}

// ---------------------------------------------------------------------------
// Leios vote body — CIP-0164 CDDL encoding
// ---------------------------------------------------------------------------

/// BLS12-381 MinSig signature size (compressed G1).
const BLS_SIGNATURE_BYTES: usize = 48;

/// Decoded Leios vote body per CIP-0164.
///
/// ```cddl
/// persistent_vote     = [0, election_id, voter_id, endorser_block_hash, vote_sig]
/// non_persistent_vote = [1, election_id, pool_id, eligibility_sig, endorser_block_hash, vote_sig]
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct VoteBody {
    /// 0 = persistent, 1 = non-persistent.
    pub tag: u8,
    pub election_id: u64,
    /// Voter/pool identifier.
    pub voter_id: Vec<u8>,
    /// Non-persistent only: eligibility proof (BLS signature).
    pub eligibility_signature: Option<Vec<u8>>,
    /// Hash of the endorser block this vote endorses.
    pub endorser_block_hash: [u8; 32],
    /// Vote signature (BLS).
    pub vote_signature: Vec<u8>,
}

impl VoteBody {
    /// Create a persistent vote with placeholder (zero) signatures.
    pub fn stub_persistent(
        election_id: u64,
        voter_id: &[u8],
        endorser_block_hash: &[u8; 32],
    ) -> Self {
        Self {
            tag: 0,
            election_id,
            voter_id: voter_id.to_vec(),
            eligibility_signature: None,
            endorser_block_hash: *endorser_block_hash,
            vote_signature: vec![0u8; BLS_SIGNATURE_BYTES],
        }
    }

    /// Create a non-persistent vote with placeholder (zero) signatures.
    pub fn stub_non_persistent(
        election_id: u64,
        voter_id: &[u8],
        endorser_block_hash: &[u8; 32],
    ) -> Self {
        Self {
            tag: 1,
            election_id,
            voter_id: voter_id.to_vec(),
            eligibility_signature: Some(vec![0u8; BLS_SIGNATURE_BYTES]),
            endorser_block_hash: *endorser_block_hash,
            vote_signature: vec![0u8; BLS_SIGNATURE_BYTES],
        }
    }

    /// Encode to CBOR, padded to at least `min_bytes`.
    pub fn encode(&self, min_bytes: usize) -> Vec<u8> {
        let mut buf = Vec::with_capacity(min_bytes);
        let mut enc = minicbor::Encoder::new(&mut buf);

        if self.tag == 0 {
            let _ = enc
                .array(5)
                .and_then(|e| e.u8(0))
                .and_then(|e| e.u64(self.election_id))
                .and_then(|e| e.bytes(&self.voter_id))
                .and_then(|e| e.bytes(&self.endorser_block_hash))
                .and_then(|e| e.bytes(&self.vote_signature));
        } else {
            let elig = self
                .eligibility_signature
                .as_deref()
                .unwrap_or(&[0u8; BLS_SIGNATURE_BYTES]);
            let _ = enc
                .array(6)
                .and_then(|e| e.u8(1))
                .and_then(|e| e.u64(self.election_id))
                .and_then(|e| e.bytes(&self.voter_id))
                .and_then(|e| e.bytes(elig))
                .and_then(|e| e.bytes(&self.endorser_block_hash))
                .and_then(|e| e.bytes(&self.vote_signature));
        }

        if buf.len() < min_bytes {
            buf.resize(min_bytes, 0);
        }
        buf
    }

    /// Decode from CBOR. Returns `None` if malformed.
    #[allow(dead_code)] // used by future vote aggregation
    pub fn decode(data: &[u8]) -> Option<Self> {
        let mut dec = minicbor::Decoder::new(data);
        let len = dec.array().ok()??;
        let tag = dec.u8().ok()?;

        match tag {
            0 if len >= 5 => {
                let election_id = dec.u64().ok()?;
                let voter_id = dec.bytes().ok()?.to_vec();
                let eb_hash_bytes = dec.bytes().ok()?;
                if eb_hash_bytes.len() < 32 {
                    return None;
                }
                let mut endorser_block_hash = [0u8; 32];
                endorser_block_hash.copy_from_slice(&eb_hash_bytes[..32]);
                let vote_signature = dec.bytes().ok()?.to_vec();
                Some(Self {
                    tag,
                    election_id,
                    voter_id,
                    eligibility_signature: None,
                    endorser_block_hash,
                    vote_signature,
                })
            }
            1 if len >= 6 => {
                let election_id = dec.u64().ok()?;
                let voter_id = dec.bytes().ok()?.to_vec();
                let eligibility_signature = Some(dec.bytes().ok()?.to_vec());
                let eb_hash_bytes = dec.bytes().ok()?;
                if eb_hash_bytes.len() < 32 {
                    return None;
                }
                let mut endorser_block_hash = [0u8; 32];
                endorser_block_hash.copy_from_slice(&eb_hash_bytes[..32]);
                let vote_signature = dec.bytes().ok()?.to_vec();
                Some(Self {
                    tag,
                    election_id,
                    voter_id,
                    eligibility_signature,
                    endorser_block_hash,
                    vote_signature,
                })
            }
            _ => None,
        }
    }
}

/// Produces fake blocks based on a VRF lottery.
pub struct BlockProducer {
    rng: StdRng,
    stake: u64,
    total_stake: u64,
    stage_length_slots: u64,
    dyn_config: watch::Receiver<DynamicConfig>,
    block_count: u64,
    eb_count: u64,
    #[allow(dead_code)]
    vote_count: u64,
}

impl BlockProducer {
    /// Create a new producer. If `seed` is None, uses entropy.
    pub fn new(
        config: &ProductionConfig,
        seed: Option<u64>,
        dyn_config: watch::Receiver<DynamicConfig>,
    ) -> Self {
        let rng = match seed {
            Some(s) => StdRng::seed_from_u64(s),
            None => StdRng::from_entropy(),
        };
        Self {
            rng,
            stake: config.stake,
            total_stake: config.total_stake,
            stage_length_slots: config.stage_length_slots,
            dyn_config,
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

        let rb_prob = self.dyn_config.borrow().rb_generation_probability;
        if !self.run_lottery(rb_prob) {
            return None;
        }

        self.block_count += 1;
        Some(self.make_fake_block(slot, prev_hash, block_number))
    }

    /// Try to produce a Leios endorser block. Called at stage boundaries.
    pub fn try_produce_eb(&mut self, slot: u64) -> Option<ProducedEb> {
        let eb_prob = self.dyn_config.borrow().eb_generation_probability;
        if !self.is_active() || eb_prob <= 0.0 {
            return None;
        }

        if !self.run_lottery(eb_prob) {
            return None;
        }

        self.eb_count += 1;

        let mut hash = [0u8; 32];
        self.rng.fill(&mut hash);
        let point = Point::Specific { slot, hash };
        let data = vec![0x82, slot as u8, 0x00]; // minimal CBOR

        Some(ProducedEb { point, data })
    }

    /// Try to produce Leios votes. Legacy stage-boundary path.
    #[allow(dead_code)] // kept for reference; voting now in consensus layer
    pub fn try_produce_votes(&mut self, slot: u64) -> Option<ProducedVotes> {
        let vote_prob = self.dyn_config.borrow().vote_generation_probability;
        if !self.is_active() || vote_prob <= 0.0 {
            return None;
        }

        if !self.run_lottery(vote_prob) {
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
        self.stage_length_slots > 0 && slot.is_multiple_of(self.stage_length_slots)
    }

    /// Number of Praos blocks produced so far.
    pub fn block_count(&self) -> u64 {
        self.block_count
    }

    /// Run the VRF lottery for a given success rate. Returns true on win.
    fn run_lottery(&mut self, probability: f64) -> bool {
        let per_node = probability * self.stake as f64 / self.total_stake as f64;
        let roll: f64 = self.rng.gen();
        roll < per_node
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

    /// Create a watch receiver with the given production config's dynamic values.
    fn dyn_rx(config: &ProductionConfig) -> watch::Receiver<DynamicConfig> {
        let dyn_config = DynamicConfig {
            rb_generation_probability: config.rb_generation_probability,
            eb_generation_probability: config.eb_generation_probability,
            vote_generation_probability: config.vote_generation_probability,
            rb_head_validation_ms: 1.0,
            rb_body_validation_ms_constant: 1000.0,
            rb_body_validation_ms_per_byte: 0.0,
            eb_validation_ms: 2.0,
            vote_validation_ms: 1.0,
            tx_rate: 0.0,
        };
        watch::channel(dyn_config).1
    }

    #[test]
    fn zero_stake_never_produces() {
        let config = base_config();
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
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
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
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
            let mut producer = BlockProducer::new(&config, Some(seed), dyn_rx(&config));
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
        let mut producer = BlockProducer::new(&config, Some(99), dyn_rx(&config));
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
    fn stage_boundary_detection() {
        let config = ProductionConfig {
            stage_length_slots: 20,
            ..base_config()
        };
        let producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
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
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
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
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
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
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
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

    #[test]
    fn vote_body_persistent_size() {
        let eb_hash = [0xAA; 32];
        let vote = VoteBody::stub_persistent(42, &[0xBB; 32], &eb_hash);
        let encoded = vote.encode(130);
        assert_eq!(encoded.len(), 130);
    }

    #[test]
    fn vote_body_non_persistent_size() {
        let eb_hash = [0xAA; 32];
        let vote = VoteBody::stub_non_persistent(42, &[0xBB; 32], &eb_hash);
        let encoded = vote.encode(180);
        assert_eq!(encoded.len(), 180);
    }

    #[test]
    fn vote_body_persistent_roundtrip() {
        let eb_hash = [0xCC; 32];
        let voter = [0xDD; 32];
        let vote = VoteBody::stub_persistent(99, &voter, &eb_hash);
        let encoded = vote.encode(200);
        let decoded = VoteBody::decode(&encoded).expect("should decode");
        assert_eq!(decoded.tag, 0);
        assert_eq!(decoded.election_id, 99);
        assert_eq!(decoded.voter_id, voter.to_vec());
        assert_eq!(decoded.endorser_block_hash, eb_hash);
        assert!(decoded.eligibility_signature.is_none());
        assert_eq!(decoded.vote_signature.len(), 48);
    }

    #[test]
    fn vote_body_non_persistent_roundtrip() {
        let eb_hash = [0x11; 32];
        let voter = [0x22; 32];
        let vote = VoteBody::stub_non_persistent(7, &voter, &eb_hash);
        let encoded = vote.encode(180);
        let decoded = VoteBody::decode(&encoded).expect("should decode");
        assert_eq!(decoded.tag, 1);
        assert_eq!(decoded.election_id, 7);
        assert_eq!(decoded.voter_id, voter.to_vec());
        assert_eq!(decoded.endorser_block_hash, eb_hash);
        assert!(decoded.eligibility_signature.is_some());
        assert_eq!(decoded.vote_signature.len(), 48);
    }

    #[test]
    fn vote_body_decode_rejects_garbage() {
        assert!(VoteBody::decode(&[0xFF, 0x00]).is_none());
        assert!(VoteBody::decode(&[]).is_none());
    }

    #[test]
    fn dynamic_update_changes_production_rate() {
        let config = ProductionConfig {
            stake: 1000,
            rb_generation_probability: 0.0, // starts at 0 — no production
            ..base_config()
        };
        let dyn_config = DynamicConfig {
            rb_generation_probability: 0.0,
            eb_generation_probability: 0.0,
            vote_generation_probability: 0.0,
            rb_head_validation_ms: 1.0,
            rb_body_validation_ms_constant: 1000.0,
            rb_body_validation_ms_per_byte: 0.0,
            eb_validation_ms: 2.0,
            vote_validation_ms: 1.0,
            tx_rate: 0.0,
        };
        let (tx, rx) = watch::channel(dyn_config);
        let mut producer = BlockProducer::new(&config, Some(42), rx);

        // Should not produce with probability 0.
        let wins_before: usize = (0..100)
            .filter(|slot| producer.try_produce_block(*slot, None, 1).is_some())
            .count();
        assert_eq!(wins_before, 0);

        // Update probability to 1.0.
        tx.send_modify(|c| {
            c.rb_generation_probability = 1.0;
        });

        // Now should always produce.
        let wins_after: usize = (100..200)
            .filter(|slot| producer.try_produce_block(*slot, None, 1).is_some())
            .count();
        assert_eq!(wins_after, 100);
    }
}
