//! Block production via fake VRF lottery.
//!
//! Each slot, the producer runs a stake-weighted lottery to decide whether
//! to produce ranking blocks (Praos), endorser blocks, and
//! votes (Leios). The lottery is ported from sim-rs.

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tokio::sync::watch;

use net_core::protocols::txsubmission::PendingTx;
use net_core::types::{BlockBody, Point, WrappedHeader};

use crate::config::{DynamicConfig, ProductionConfig};

/// A produced Leios endorser block.
pub struct ProducedEb {
    pub point: Point,
    pub data: Vec<u8>,
}

// ---------------------------------------------------------------------------
// Leios vote body — CIP-0164 CDDL encoding
// ---------------------------------------------------------------------------

/// BLS12-381 MinSig signature size (compressed G1).
const BLS_SIGNATURE_BYTES: usize = 48;

/// Decoded Leios vote body per CIP-0164.
///
/// ```cddl
/// persistent_vote     = [0, election_id, voter_id, voter_stake, endorser_block_hash, vote_sig]
/// non_persistent_vote = [1, election_id, pool_id, voter_stake, eligibility_sig, endorser_block_hash, vote_sig]
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct VoteBody {
    /// 0 = persistent, 1 = non-persistent.
    pub tag: u8,
    pub election_id: u64,
    /// Voter/pool identifier.
    pub voter_id: Vec<u8>,
    /// Voter's stake weight (for stake-weighted quorum).
    pub voter_stake: u64,
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
        voter_stake: u64,
        endorser_block_hash: &[u8; 32],
    ) -> Self {
        Self {
            tag: 0,
            election_id,
            voter_id: voter_id.to_vec(),
            voter_stake,
            eligibility_signature: None,
            endorser_block_hash: *endorser_block_hash,
            vote_signature: vec![0u8; BLS_SIGNATURE_BYTES],
        }
    }

    /// Create a non-persistent vote with placeholder (zero) signatures.
    pub fn stub_non_persistent(
        election_id: u64,
        voter_id: &[u8],
        voter_stake: u64,
        endorser_block_hash: &[u8; 32],
    ) -> Self {
        Self {
            tag: 1,
            election_id,
            voter_id: voter_id.to_vec(),
            voter_stake,
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
                .array(6)
                .and_then(|e| e.u8(0))
                .and_then(|e| e.u64(self.election_id))
                .and_then(|e| e.bytes(&self.voter_id))
                .and_then(|e| e.u64(self.voter_stake))
                .and_then(|e| e.bytes(&self.endorser_block_hash))
                .and_then(|e| e.bytes(&self.vote_signature));
        } else {
            let elig = self
                .eligibility_signature
                .as_deref()
                .unwrap_or(&[0u8; BLS_SIGNATURE_BYTES]);
            let _ = enc
                .array(7)
                .and_then(|e| e.u8(1))
                .and_then(|e| e.u64(self.election_id))
                .and_then(|e| e.bytes(&self.voter_id))
                .and_then(|e| e.u64(self.voter_stake))
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
    pub fn decode(data: &[u8]) -> Option<Self> {
        let mut dec = minicbor::Decoder::new(data);
        let len = dec.array().ok()??;
        let tag = dec.u8().ok()?;

        match tag {
            0 if len >= 6 => {
                let election_id = dec.u64().ok()?;
                let voter_id = dec.bytes().ok()?.to_vec();
                let voter_stake = dec.u64().ok()?;
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
                    voter_stake,
                    eligibility_signature: None,
                    endorser_block_hash,
                    vote_signature,
                })
            }
            1 if len >= 7 => {
                let election_id = dec.u64().ok()?;
                let voter_id = dec.bytes().ok()?.to_vec();
                let voter_stake = dec.u64().ok()?;
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
                    voter_stake,
                    eligibility_signature,
                    endorser_block_hash,
                    vote_signature,
                })
            }
            _ => None,
        }
    }
}

/// Result of a successful RB production attempt.
pub struct ProducedRb {
    pub point: Point,
    pub header: WrappedHeader,
    pub body: BlockBody,
    /// If the mempool overflowed, the EB manifest to inject into the network.
    pub announced_eb: Option<ProducedEb>,
    /// Number of transactions included in the RB body (RB path only).
    pub included_tx_count: usize,
}

/// Produces fake blocks based on a VRF lottery.
pub struct BlockProducer {
    rng: StdRng,
    stake: u64,
    total_stake: u64,
    rb_body_max_bytes: usize,
    dyn_config: watch::Receiver<DynamicConfig>,
    block_count: u64,
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
            rb_body_max_bytes: config.rb_body_max_bytes,
            dyn_config,
            block_count: 0,
        }
    }

    /// Returns true if this node has any stake allocated for production.
    pub fn is_active(&self) -> bool {
        self.stake > 0 && self.total_stake > 0
    }

    /// Run the VRF lottery for a Praos ranking block. On win, drains the
    /// mempool: if pending txs fit in `rb_body_max_bytes`, they go in the
    /// RB body (RB path). Otherwise, ALL txs go into an EB manifest and
    /// the RB body is empty (EB path).
    pub fn try_produce_block(
        &mut self,
        slot: u64,
        prev_hash: Option<[u8; 32]>,
        block_number: u64,
        certified_eb: bool,
        mempool: &crate::mempool::SharedMempool,
    ) -> Option<ProducedRb> {
        if !self.is_active() {
            return None;
        }

        let rb_prob = self.dyn_config.borrow().rb_generation_probability;
        if !self.run_lottery(rb_prob) {
            return None;
        }

        self.block_count += 1;

        // Drain mempool and decide RB vs EB path.
        let mut pool = mempool.lock().unwrap();
        let (txs, announced_eb) = if pool.total_bytes() > self.rb_body_max_bytes {
            // EB path: all txs → EB manifest, RB body empty.
            let all_txs = pool.drain_all();
            let eb = make_overflow_eb(slot, &all_txs);
            (Vec::new(), Some(eb))
        } else {
            // RB path: txs in RB body, no EB.
            let txs = pool.drain_up_to(self.rb_body_max_bytes);
            (txs, None)
        };
        drop(pool);

        let eb_ref = announced_eb.as_ref().map(|eb| match eb.point {
            Point::Specific { hash, .. } => (hash, eb.data.len() as u32),
            _ => unreachable!(),
        });

        let tx_count = txs.len();
        let (point, header, body) =
            self.make_fake_block(slot, prev_hash, block_number, certified_eb, &txs, eb_ref);

        Some(ProducedRb {
            point,
            header,
            body,
            announced_eb,
            included_tx_count: tx_count,
        })
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
    /// The point hash uses `header_hash()`, matching the real Cardano
    /// derivation.
    ///
    /// CIP-0164 header field ordering (array-length disambiguation):
    ///   10 = base only
    ///   11 = base + certified_eb (bool)
    ///   12 = base + announced_eb (hash + size)
    ///   13 = base + announced_eb + certified_eb
    fn make_fake_block(
        &mut self,
        slot: u64,
        prev_hash: Option<[u8; 32]>,
        block_number: u64,
        certified_eb: bool,
        txs: &[PendingTx],
        announced_eb: Option<([u8; 32], u32)>,
    ) -> (Point, WrappedHeader, BlockBody) {
        let mut issuer_vkey = [0u8; 32];
        self.rng.fill(&mut issuer_vkey);
        let mut body_hash = [0u8; 32];
        self.rng.fill(&mut body_hash);

        // Compute header array length based on optional Leios extensions.
        let extra = match (announced_eb.is_some(), certified_eb) {
            (false, false) => 0,
            (false, true) => 1,
            (true, false) => 2,
            (true, true) => 3,
        };
        let array_len: u64 = 10 + extra;

        // Compute body size from txs for the header field.
        let tx_body_size: usize = txs.iter().map(|tx| tx.size as usize).sum();

        let mut header_body = Vec::new();
        let mut hb = minicbor::Encoder::new(&mut header_body);
        let _ = hb
            .array(array_len)
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
            .and_then(|e| e.u32(tx_body_size as u32)) // body_size
            .and_then(|e| e.bytes(&body_hash)) // block_body_hash
            .and_then(|e| e.array(4)) // operational_cert
            .and_then(|e| e.bytes(&[0u8; 32]))
            .and_then(|e| e.u64(0))
            .and_then(|e| e.u64(0))
            .and_then(|e| e.bytes(&[0u8; 64]))
            .and_then(|e| e.array(2)) // protocol_version
            .and_then(|e| e.u32(10))
            .and_then(|e| e.u32(0));

        // Optional Leios fields: announced_eb first, then certified_eb.
        if let Some((eb_hash, eb_size)) = announced_eb {
            let _ = minicbor::Encoder::new(&mut header_body).bytes(&eb_hash);
            let _ = minicbor::Encoder::new(&mut header_body).u32(eb_size);
        }
        if certified_eb {
            let _ = minicbor::Encoder::new(&mut header_body).bool(true);
        }

        // Inner header: [header_body, body_signature]
        let mut header_inner = Vec::new();
        let mut hi = minicbor::Encoder::new(&mut header_inner);
        let _ = hi.array(2);
        header_inner.extend_from_slice(&header_body);
        let _ = minicbor::Encoder::new(&mut header_inner).bytes(&[0u8; 64]);

        // Header CBOR: [era_tag, #6.24(header_inner)]
        let era: u32 = 7; // Conway
        let mut header_cbor = Vec::new();
        let mut he = minicbor::Encoder::new(&mut header_cbor);
        let _ = he
            .array(2)
            .and_then(|e| e.u32(era))
            .and_then(|e| e.tag(minicbor::data::Tag::new(24)))
            .and_then(|e| e.bytes(&header_inner));

        let header = WrappedHeader::new(header_cbor.clone());
        let point = header
            .point()
            .expect("freshly-built Shelley+ header must parse");

        // Block body: #6.24([era_tag, [header, tx_bodies, tx_witnesses, metadata]])
        let mut block_inner = Vec::new();
        let mut bi = minicbor::Encoder::new(&mut block_inner);
        let _ = bi.array(2).and_then(|e| e.u32(era));
        let _ = minicbor::Encoder::new(&mut block_inner).array(4);
        block_inner.extend_from_slice(&header_inner);

        // tx_bodies: map of {index => bytes(tx_body)}
        let _ = minicbor::Encoder::new(&mut block_inner).map(txs.len() as u64);
        for (i, tx) in txs.iter().enumerate() {
            let _ = minicbor::Encoder::new(&mut block_inner).u32(i as u32);
            let _ = minicbor::Encoder::new(&mut block_inner).bytes(&tx.body.0);
        }
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

/// Build an EB manifest from overflow transactions. The EB body is a CBOR
/// array `[slot, [tx_hash, ...]]` and the point hash is Blake2b-256 of
/// the manifest bytes (content-addressed).
fn make_overflow_eb(slot: u64, txs: &[PendingTx]) -> ProducedEb {
    let mut data = Vec::new();
    let mut enc = minicbor::Encoder::new(&mut data);
    let _ = enc
        .array(2)
        .and_then(|e| e.u64(slot))
        .and_then(|e| e.array(txs.len() as u64));
    for tx in txs {
        let _ = minicbor::Encoder::new(&mut data).bytes(&tx.tx_id.0);
    }

    let hash_result = blake2b_simd::Params::new().hash_length(32).hash(&data);
    let mut hash = [0u8; 32];
    hash.copy_from_slice(hash_result.as_bytes());
    let point = Point::Specific { slot, hash };

    ProducedEb { point, data }
}

#[cfg(test)]
mod tests {
    use super::*;
    use net_core::protocols::txsubmission::{PendingTx, TxBody, TxId};

    fn base_config() -> ProductionConfig {
        ProductionConfig {
            stake: 0,
            total_stake: 1000,
            ..Default::default()
        }
    }

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

    fn empty_mempool() -> crate::mempool::SharedMempool {
        crate::mempool::new_mempool(1000)
    }

    fn make_test_tx(id: u8, size: usize) -> PendingTx {
        PendingTx {
            tx_id: TxId(vec![id; 32]),
            body: TxBody(vec![id; size]),
            size: size as u32,
        }
    }

    fn mempool_with_txs(txs: Vec<PendingTx>) -> crate::mempool::SharedMempool {
        let pool = crate::mempool::new_mempool(1000);
        {
            let mut p = pool.lock().unwrap();
            for tx in txs {
                p.push(tx);
            }
        }
        pool
    }

    // -- Lottery tests (mempool-independent) --

    #[test]
    fn zero_stake_never_produces() {
        let config = base_config();
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
        let mempool = empty_mempool();
        assert!(!producer.is_active());
        for slot in 0..100 {
            assert!(producer
                .try_produce_block(slot, None, slot + 1, false, &mempool)
                .is_none());
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
        let mempool = empty_mempool();
        assert!(producer.is_active());
        for slot in 0..100 {
            let result = producer.try_produce_block(slot, None, slot + 1, false, &mempool);
            assert!(result.is_some(), "should produce at slot {slot}");
            match result.unwrap().point {
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
            let mempool = empty_mempool();
            (0..1000)
                .filter_map(|slot| {
                    producer
                        .try_produce_block(slot, None, slot + 1, false, &mempool)
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
        let mempool = empty_mempool();
        let wins: usize = (0..10_000)
            .filter(|slot| {
                producer
                    .try_produce_block(*slot, None, 1, false, &mempool)
                    .is_some()
            })
            .count();
        assert!(
            (400..=600).contains(&wins),
            "wins={wins}, expected ~500 (5%)"
        );
    }

    // -- RB path: txs in block body --

    #[test]
    fn rb_path_includes_txs_in_body() {
        let config = ProductionConfig {
            stake: 1000,
            rb_generation_probability: 1.0,
            rb_body_max_bytes: 65536,
            ..base_config()
        };
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
        let mempool = mempool_with_txs(vec![make_test_tx(1, 500), make_test_tx(2, 300)]);

        let produced = producer
            .try_produce_block(100, None, 1, false, &mempool)
            .unwrap();

        assert_eq!(produced.included_tx_count, 2);
        assert!(produced.announced_eb.is_none());
        // body.point() must still work with txs embedded.
        assert!(produced.body.point().is_some());
        assert_eq!(produced.body.point().unwrap(), produced.point);
        // Body should be larger than an empty block.
        assert!(produced.body.raw.len() > 500);
    }

    #[test]
    fn empty_mempool_empty_block() {
        let config = ProductionConfig {
            stake: 1000,
            rb_generation_probability: 1.0,
            ..base_config()
        };
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
        let mempool = empty_mempool();

        let produced = producer
            .try_produce_block(100, None, 1, false, &mempool)
            .unwrap();

        assert_eq!(produced.included_tx_count, 0);
        assert!(produced.announced_eb.is_none());
        assert!(produced.body.point().is_some());
    }

    // -- EB path: overflow --

    #[test]
    fn eb_path_on_overflow() {
        let config = ProductionConfig {
            stake: 1000,
            rb_generation_probability: 1.0,
            rb_body_max_bytes: 1000, // 1KB limit
            ..base_config()
        };
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
        // 3 txs totaling 1500 bytes — exceeds 1000 byte limit.
        let mempool = mempool_with_txs(vec![
            make_test_tx(1, 500),
            make_test_tx(2, 500),
            make_test_tx(3, 500),
        ]);

        let produced = producer
            .try_produce_block(100, None, 1, false, &mempool)
            .unwrap();

        // EB path: RB body is empty, EB is announced.
        assert_eq!(produced.included_tx_count, 0);
        assert!(produced.announced_eb.is_some());
        assert!(produced.body.point().is_some());

        // announced_eb should appear in the header.
        let info = produced.header.parsed.as_ref().unwrap();
        assert!(info.announced_eb.is_some());
        let (eb_hash, eb_size) = info.announced_eb.unwrap();
        let eb = produced.announced_eb.unwrap();
        match eb.point {
            Point::Specific { hash, .. } => assert_eq!(hash, eb_hash),
            _ => panic!("expected Specific point"),
        }
        assert_eq!(eb.data.len() as u32, eb_size);

        // Mempool should be drained.
        assert_eq!(mempool.lock().unwrap().len(), 0);
    }

    #[test]
    fn overflow_eb_is_content_addressed() {
        let txs = vec![make_test_tx(1, 100), make_test_tx(2, 200)];
        let eb1 = make_overflow_eb(50, &txs);
        let eb2 = make_overflow_eb(50, &txs);
        match (&eb1.point, &eb2.point) {
            (Point::Specific { hash: h1, .. }, Point::Specific { hash: h2, .. }) => {
                assert_eq!(h1, h2, "same inputs should produce same hash");
            }
            _ => panic!("expected Specific points"),
        }
    }

    #[test]
    fn overflow_eb_encodes_tx_hashes() {
        let txs = vec![make_test_tx(0xAA, 100), make_test_tx(0xBB, 200)];
        let eb = make_overflow_eb(42, &txs);

        // Decode the manifest: [slot, [hash, ...]]
        let mut dec = minicbor::Decoder::new(&eb.data);
        let outer_len = dec.array().unwrap().unwrap();
        assert_eq!(outer_len, 2);
        let slot = dec.u64().unwrap();
        assert_eq!(slot, 42);
        let inner_len = dec.array().unwrap().unwrap();
        assert_eq!(inner_len, 2);
        let hash1 = dec.bytes().unwrap();
        assert_eq!(hash1, &[0xAA; 32]);
        let hash2 = dec.bytes().unwrap();
        assert_eq!(hash2, &[0xBB; 32]);
    }

    // -- Header roundtrip tests --

    #[test]
    fn fake_block_has_parseable_cbor() {
        let config = ProductionConfig {
            stake: 1000,
            rb_generation_probability: 1.0,
            ..base_config()
        };
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
        let mempool = empty_mempool();
        let produced = producer
            .try_produce_block(12345, None, 1, false, &mempool)
            .unwrap();

        assert!(produced.header.parsed.is_some(), "header should parse");
        let info = produced.header.parsed.as_ref().unwrap();
        assert_eq!(info.slot, 12345);
        assert_eq!(info.era, 7);
        assert_eq!(produced.header.point().unwrap(), produced.point);
        assert_eq!(produced.body.point().unwrap(), produced.point);
        let extracted = produced.body.header().unwrap();
        assert_eq!(extracted.parsed.as_ref().unwrap().slot, 12345);
    }

    #[test]
    fn certified_eb_header_roundtrips() {
        let config = ProductionConfig {
            stake: 1000,
            total_stake: 1000,
            rb_generation_probability: 1.0,
            ..base_config()
        };
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
        let mempool = empty_mempool();
        let produced = producer
            .try_produce_block(100, None, 1, true, &mempool)
            .unwrap();

        let info = produced.header.parsed.as_ref().unwrap();
        assert_eq!(info.certified_eb, Some(true));
    }

    #[test]
    fn no_certified_eb_when_false() {
        let config = ProductionConfig {
            stake: 1000,
            total_stake: 1000,
            rb_generation_probability: 1.0,
            ..base_config()
        };
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
        let mempool = empty_mempool();
        let produced = producer
            .try_produce_block(100, None, 1, false, &mempool)
            .unwrap();

        let info = produced.header.parsed.as_ref().unwrap();
        assert_eq!(info.certified_eb, None);
    }

    #[test]
    fn announced_eb_plus_certified_eb() {
        let config = ProductionConfig {
            stake: 1000,
            total_stake: 1000,
            rb_generation_probability: 1.0,
            rb_body_max_bytes: 100, // force overflow
            ..base_config()
        };
        let mut producer = BlockProducer::new(&config, Some(42), dyn_rx(&config));
        let mempool = mempool_with_txs(vec![make_test_tx(1, 200)]);

        let produced = producer
            .try_produce_block(100, None, 1, true, &mempool)
            .unwrap();

        let info = produced.header.parsed.as_ref().unwrap();
        assert!(info.announced_eb.is_some(), "should have announced_eb");
        assert_eq!(info.certified_eb, Some(true), "should have certified_eb");
    }

    #[test]
    fn dynamic_update_changes_production_rate() {
        let config = ProductionConfig {
            stake: 1000,
            rb_generation_probability: 0.0,
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
        let mempool = empty_mempool();

        let wins_before: usize = (0..100)
            .filter(|slot| {
                producer
                    .try_produce_block(*slot, None, 1, false, &mempool)
                    .is_some()
            })
            .count();
        assert_eq!(wins_before, 0);

        tx.send_modify(|c| {
            c.rb_generation_probability = 1.0;
        });

        let wins_after: usize = (100..200)
            .filter(|slot| {
                producer
                    .try_produce_block(*slot, None, 1, false, &mempool)
                    .is_some()
            })
            .count();
        assert_eq!(wins_after, 100);
    }

    // -- Vote body tests (unchanged) --

    #[test]
    fn vote_body_persistent_size() {
        let eb_hash = [0xAA; 32];
        let vote = VoteBody::stub_persistent(42, &[0xBB; 32], 100, &eb_hash);
        let encoded = vote.encode(130);
        assert_eq!(encoded.len(), 130);
    }

    #[test]
    fn vote_body_non_persistent_size() {
        let eb_hash = [0xAA; 32];
        let vote = VoteBody::stub_non_persistent(42, &[0xBB; 32], 100, &eb_hash);
        let encoded = vote.encode(180);
        assert_eq!(encoded.len(), 180);
    }

    #[test]
    fn vote_body_persistent_roundtrip() {
        let eb_hash = [0xCC; 32];
        let voter = [0xDD; 32];
        let vote = VoteBody::stub_persistent(99, &voter, 500, &eb_hash);
        let encoded = vote.encode(200);
        let decoded = VoteBody::decode(&encoded).expect("should decode");
        assert_eq!(decoded.tag, 0);
        assert_eq!(decoded.election_id, 99);
        assert_eq!(decoded.voter_id, voter.to_vec());
        assert_eq!(decoded.voter_stake, 500);
        assert_eq!(decoded.endorser_block_hash, eb_hash);
        assert!(decoded.eligibility_signature.is_none());
        assert_eq!(decoded.vote_signature.len(), 48);
    }

    #[test]
    fn vote_body_non_persistent_roundtrip() {
        let eb_hash = [0x11; 32];
        let voter = [0x22; 32];
        let vote = VoteBody::stub_non_persistent(7, &voter, 250, &eb_hash);
        let encoded = vote.encode(180);
        let decoded = VoteBody::decode(&encoded).expect("should decode");
        assert_eq!(decoded.tag, 1);
        assert_eq!(decoded.election_id, 7);
        assert_eq!(decoded.voter_id, voter.to_vec());
        assert_eq!(decoded.voter_stake, 250);
        assert_eq!(decoded.endorser_block_hash, eb_hash);
        assert!(decoded.eligibility_signature.is_some());
        assert_eq!(decoded.vote_signature.len(), 48);
    }

    #[test]
    fn vote_body_decode_rejects_garbage() {
        assert!(VoteBody::decode(&[0xFF, 0x00]).is_none());
        assert!(VoteBody::decode(&[]).is_none());
    }
}
