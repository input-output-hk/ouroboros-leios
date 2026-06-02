//! Block production via fake VRF lottery.
//!
//! Each slot, the producer runs a stake-weighted lottery to decide whether
//! to produce ranking blocks (Praos), endorser blocks, and
//! votes (Leios). The lottery is ported from sim-rs.

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tokio::sync::watch;

use shared_consensus::mempool::EbKey;
use net_core::protocols::txsubmission::PendingTx;
use net_core::types::{BlockBody, Point, WrappedHeader};

use crate::config::{DynamicConfig, ProductionConfig};

/// A produced Leios endorser block.  The bodies of the referenced
/// transactions stay pinned in the mempool under the EB's key — peers
/// fetch them via `MsgLeiosBlockTxsRequest`, served through the
/// LeiosStore's `TxBodyResolver` fallback path.
pub struct ProducedEb {
    pub point: Point,
    /// CBOR-encoded manifest `[slot, [tx_hash, ...]]`.
    pub data: Vec<u8>,
}

/// Result of a successful RB production attempt.
pub struct ProducedRb {
    pub point: Point,
    pub header: WrappedHeader,
    pub body: BlockBody,
    /// If the mempool overflowed, the EB manifest to inject into the network.
    pub announced_eb: Option<ProducedEb>,
    /// Number of transactions included inline in the RB body.  Non-zero
    /// for the pure-RB case and the RB+EB overflow split alike;
    /// the EB-announcement residual (if any) is counted by
    /// `announced_eb`, not here.
    pub included_tx_count: usize,
}

/// Produces fake blocks based on a VRF lottery.
pub struct BlockProducer {
    rng: StdRng,
    stake: u64,
    total_stake: u64,
    rb_body_max_bytes: usize,
    eb_body_max_bytes: usize,
    dyn_config: watch::Receiver<DynamicConfig>,
    block_count: u64,
    /// Issuer vkey used by `make_fake_block`.  Refreshed at the top of
    /// every honest production call; the equivocation-extra path reuses
    /// the unchanged value so the duplicate header shares the issuer
    /// (CIP-0164 equivocation requires same-issuer same-slot distinct
    /// headers).
    last_issuer_vkey: [u8; 32],
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
            eb_body_max_bytes: config.eb_body_max_bytes,
            dyn_config,
            block_count: 0,
            last_issuer_vkey: [0u8; 32],
        }
    }

    /// Returns true if this node has any stake allocated for production.
    pub fn is_active(&self) -> bool {
        self.stake > 0 && self.total_stake > 0
    }

    /// Run the VRF lottery for a Praos ranking block. On win, asks
    /// shared-consensus's `production::BodyPath::decide` how to split
    /// the pending mempool between the RB body and a fresh EB
    /// announcement:
    ///
    /// - All-fits case: every pending tx goes inline into the RB body
    ///   up to `rb_body_max_bytes`; no EB is announced.
    /// - Overflow split: txs fill the RB body up to `rb_body_max_bytes`
    ///   and the residual is announced via a fresh EB whose
    ///   FIFO-ordered manifest is capped at `eb_body_max_bytes` worth
    ///   of tx bodies.  Inline RB body and EB announcement coexist;
    ///   anything past both caps stays in the mempool for the next RB.
    /// - Empty-for-safety: the producer-side EB-safety gate may force
    ///   both inline and announcement to be empty (no EB is announced
    ///   when the chain context can't certify one safely).
    pub fn try_produce_block(
        &mut self,
        slot: u64,
        prev_hash: Option<[u8; 32]>,
        block_number: u64,
        certified_eb: bool,
        mempool: &crate::mempool::SharedMempool,
        leios: &shared_consensus::leios::LeiosState,
    ) -> Option<ProducedRb> {
        if !self.is_active() {
            return None;
        }

        let rb_prob = self.dyn_config.borrow().rb_generation_probability;
        if !self.run_lottery(rb_prob) {
            return None;
        }

        // Fresh issuer for this slot's honest block; equivocation
        // extras then reuse the same value.
        self.rng.fill(&mut self.last_issuer_vkey);

        self.block_count += 1;

        // CIP-0164 overflow rule plus producer-side EB-safety gate
        // both live in shared-consensus (`production::BodyPath`).  The
        // returned struct's `inline` becomes the RB body and
        // `manifest_hashes` becomes a fresh EB announcement; either
        // (or both) may be empty.
        let mut pool = mempool.lock().unwrap();
        let body_path = pool.decide_body_path(
            self.rb_body_max_bytes,
            self.eb_body_max_bytes,
            leios,
            certified_eb,
        );
        let txs = body_path.inline;
        let announced_eb = if body_path.manifest_hashes.is_empty() {
            None
        } else {
            // Encode wire bytes, hash them, then commit the
            // drain-and-pin under the resulting EB key.  Bodies stay
            // pinned in the mempool under `eb_pinned` so the producer
            // can vote for its own EB (MissingTX predicate sees them)
            // and serve `LeiosFetch BlockTxs` (resolver finds them by
            // tx_id).
            let manifest_len = body_path.manifest_hashes.len();
            let eb_data = encode_overflow_eb(slot, &body_path.manifest_hashes);
            let eb_hash = blake2b_256(&eb_data);
            let eb_key = EbKey {
                slot,
                hash: eb_hash,
            };
            pool.produce_eb(eb_key, manifest_len);
            Some(ProducedEb {
                point: Point::Specific {
                    slot,
                    hash: eb_hash,
                },
                data: eb_data,
            })
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

    /// Produce a duplicate RB for the same lottery win, with the same
    /// issuer and slot as `primary` but a fresh body — yields a
    /// distinct header hash that triggers CIP-0164 RB-header
    /// equivocation detection on every honest peer.  Used by the
    /// `RbHeaderEquivocator` behaviour via the wrapper's
    /// [`RbProductionStrategy::Equivocate`] branch.
    pub fn produce_equivocation_extra(
        &mut self,
        primary: &ProducedRb,
        prev_hash: Option<[u8; 32]>,
        block_number: u64,
    ) -> ProducedRb {
        let slot = match primary.point {
            Point::Specific { slot, .. } => slot,
            Point::Origin => unreachable!("primary RB is never at Origin"),
        };
        // Reuse `self.last_issuer_vkey` (still the primary's issuer)
        // and use an empty body — different body_hash → different
        // block_hash → different header_hash, but same (slot, issuer)
        // so the detection rule fires.
        let (point, header, body) =
            self.make_fake_block(slot, prev_hash, block_number, false, &[], None);
        ProducedRb {
            point,
            header,
            body,
            announced_eb: None,
            included_tx_count: 0,
        }
    }

    /// Run the Praos f_block lottery.  Returns true on win.  Threshold
    /// math lives in [`shared_consensus::lottery::LotteryParams`]; this site
    /// supplies the `u64` draw.  When a real VRF replaces the PRNG, only
    /// the draw source changes — the integer comparison stays.
    fn run_lottery(&mut self, probability: f64) -> bool {
        let params = shared_consensus::lottery::LotteryParams::new(probability);
        let threshold = params.rb_win_threshold(self.stake, self.total_stake);
        let draw: u64 = self.rng.gen();
        draw < threshold
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
        // `last_issuer_vkey` is refreshed by `try_produce_block` at the
        // start of every honest call; equivocation-extra reuses the
        // previous value.
        let issuer_vkey = self.last_issuer_vkey;
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

        // tx_bodies: `[* transaction_body]` per Cardano CDDL.
        let _ = minicbor::Encoder::new(&mut block_inner).array(txs.len() as u64);
        for tx in txs.iter() {
            let _ = minicbor::Encoder::new(&mut block_inner).bytes(&tx.body.0);
        }
        // tx_witnesses: `[* transaction_witness_set]` per Cardano CDDL.
        let _ = minicbor::Encoder::new(&mut block_inner).array(0);
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

/// Decode an overflow EB manifest produced by `make_overflow_eb`.
/// Returns `(slot, tx_hashes)` on success, where each `tx_hash` is 32 bytes.
pub fn decode_overflow_eb(blob: &[u8]) -> Option<(u64, Vec<[u8; 32]>)> {
    let mut dec = minicbor::Decoder::new(blob);
    let outer = dec.array().ok()??;
    if outer != 2 {
        return None;
    }
    let slot = dec.u64().ok()?;
    let inner = dec.array().ok()??;
    let mut hashes = Vec::with_capacity(inner as usize);
    for _ in 0..inner {
        let bytes = dec.bytes().ok()?;
        if bytes.len() != 32 {
            return None;
        }
        let mut h = [0u8; 32];
        h.copy_from_slice(bytes);
        hashes.push(h);
    }
    Some((slot, hashes))
}

/// Encode an EB body as CBOR `[slot, [tx_hash, ...]]` — pure function
/// over the manifest hashes; lets the caller hash the bytes to derive
/// the EB key before committing the drain in the mempool.
pub fn encode_overflow_eb(slot: u64, manifest: &[[u8; 32]]) -> Vec<u8> {
    let mut data = Vec::new();
    let mut enc = minicbor::Encoder::new(&mut data);
    let _ = enc
        .array(2)
        .and_then(|e| e.u64(slot))
        .and_then(|e| e.array(manifest.len() as u64));
    for h in manifest {
        let _ = minicbor::Encoder::new(&mut data).bytes(h);
    }
    data
}

/// Blake2b-256 of arbitrary bytes — matches the EB-key derivation used
/// across the wire and the `tx_from_received_bytes` tx-id derivation.
pub fn blake2b_256(bytes: &[u8]) -> [u8; 32] {
    let result = blake2b_simd::Params::new().hash_length(32).hash(bytes);
    let mut out = [0u8; 32];
    out.copy_from_slice(result.as_bytes());
    out
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

    /// Minimal `LeiosState` for tests that don't exercise the
    /// producer-side EB-safety gate — `has_endorsed_unvalidated_eb`
    /// is false on a fresh state, so `BodyPath::decide` falls through
    /// to the regular overflow rule.
    fn empty_leios() -> shared_consensus::leios::LeiosState {
        use shared_consensus::config::CommitteeSelection;
        use shared_consensus::elections::{Elections, ElectionsConfig};
        use shared_consensus::leios::{LeiosState, VotingConfig};
        use shared_consensus::pipeline::PipelineConfig;
        use std::collections::BTreeMap;

        let pipeline = PipelineConfig {
            delta_hdr: 1,
            vote_window: 5,
            diffuse_window: 5,
            dedup_window: 10,
        };
        let elections = Elections::new(ElectionsConfig {
            node_id: "test".to_string(),
            pipeline,
            committee_selection: CommitteeSelection::EveryoneVotes,
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 1000,
            expected_total_weight: 100,
            quorum_weight_fraction: 0.75,
        });
        let voting = VotingConfig {
            committee_selection: CommitteeSelection::EveryoneVotes,
            stake: 100,
            total_stake: 1000,
            persistent_vote_bytes: 130,
            non_persistent_vote_bytes: 180,
            persistent_seats: 1,
            retry_vote_in_window: true,
        };
        LeiosState::new("test".into(), elections, voting, pipeline)
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
                .try_produce_block(slot, None, slot + 1, false, &mempool, &empty_leios())
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
            let result = producer.try_produce_block(slot, None, slot + 1, false, &mempool, &empty_leios());
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
                        .try_produce_block(slot, None, slot + 1, false, &mempool, &empty_leios())
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
        // Expected win rate per slot is the spec-faithful Praos
        // φ(σ) = 1 − (1 − f)^σ.  For stake=100, total_stake=1000, f=0.5:
        // φ = 1 − 0.5^0.1 ≈ 0.0670, so ~670 wins out of 10 000 slots.
        // Bounds span 4σ (≈100 wins) of binomial variance to keep the
        // test stable across PRNG seeds.
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
                    .try_produce_block(*slot, None, 1, false, &mempool, &empty_leios())
                    .is_some()
            })
            .count();
        assert!(
            (570..=770).contains(&wins),
            "wins={wins}, expected ~670 (6.7%)"
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
            .try_produce_block(100, None, 1, false, &mempool, &empty_leios())
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
            .try_produce_block(100, None, 1, false, &mempool, &empty_leios())
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
            .try_produce_block(100, None, 1, false, &mempool, &empty_leios())
            .unwrap();

        // CIP-0164 overflow: drain RB body up to the cap (2 × 500 =
        // 1000 fits exactly), residual (the third 500-byte tx) is
        // announced via the EB.
        assert_eq!(produced.included_tx_count, 2);
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

        // Mempool drained: 2 inline + 1 pinned in the EB closure.
        assert_eq!(mempool.lock().unwrap().len(), 0);
    }

    #[test]
    fn encode_overflow_eb_is_deterministic() {
        let manifest = vec![[0x10u8; 32], [0x20u8; 32]];
        let a = encode_overflow_eb(50, &manifest);
        let b = encode_overflow_eb(50, &manifest);
        assert_eq!(a, b);
        assert_eq!(blake2b_256(&a), blake2b_256(&b));
    }

    #[test]
    fn decode_overflow_eb_round_trip() {
        let manifest = vec![[0x10u8; 32], [0x20u8; 32]];
        let data = encode_overflow_eb(99, &manifest);
        let (slot, hashes) = decode_overflow_eb(&data).expect("decode");
        assert_eq!(slot, 99);
        assert_eq!(hashes, manifest);
    }

    #[test]
    fn decode_overflow_eb_rejects_garbage() {
        assert!(decode_overflow_eb(&[0xFF, 0xFF]).is_none());
        assert!(decode_overflow_eb(&[]).is_none());
    }

    #[test]
    fn encode_overflow_eb_layout() {
        let manifest = vec![[0xAAu8; 32], [0xBBu8; 32]];
        let data = encode_overflow_eb(42, &manifest);
        // Decode the manifest: [slot, [hash, ...]]
        let mut dec = minicbor::Decoder::new(&data);
        let outer_len = dec.array().unwrap().unwrap();
        assert_eq!(outer_len, 2);
        let slot = dec.u64().unwrap();
        assert_eq!(slot, 42);
        let inner_len = dec.array().unwrap().unwrap();
        assert_eq!(inner_len, 2);
        assert_eq!(dec.bytes().unwrap(), &[0xAA; 32]);
        assert_eq!(dec.bytes().unwrap(), &[0xBB; 32]);
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
            .try_produce_block(12345, None, 1, false, &mempool, &empty_leios())
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
            .try_produce_block(100, None, 1, true, &mempool, &empty_leios())
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
            .try_produce_block(100, None, 1, false, &mempool, &empty_leios())
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
            .try_produce_block(100, None, 1, true, &mempool, &empty_leios())
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
                    .try_produce_block(*slot, None, 1, false, &mempool, &empty_leios())
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
                    .try_produce_block(*slot, None, 1, false, &mempool, &empty_leios())
                    .is_some()
            })
            .count();
        assert_eq!(wins_after, 100);
    }

}
