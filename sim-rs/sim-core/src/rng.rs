//! Stateless, context-derived pseudo-randomness for the simulator.
//!
//! Every random draw is a pure function of `(global_seed, context)`. There
//! is no evolving per-node RNG state: whether node N draws 0 or 600 times
//! in slot S doesn't affect any draw in slot S+1 (or any other node's draws
//! at any slot). This mirrors the real Cardano VRF — `vrf_output = f(key,
//! nonce || slot)` is a pure function — and eliminates the class of
//! non-determinism bugs where upstream timing drift desynchronises a
//! node's RNG state and cascades into every downstream random decision.
//!
//! Use: construct an `Rng` once from the simulation seed, share it via
//! `Arc` or `Clone`, and call `draw_*` methods with an explicit context
//! (usually `(NodeId, slot, DrawSite)` via the convenience wrappers).
//!
//! Collision resistance: different `DrawSite` variants produce distinct
//! hashes by construction (the derive-Hash impl mixes in the variant
//! discriminant). Picking the same `DrawSite` with the same `(node, slot)`
//! is the caller's responsibility — add a new variant or a field (e.g. a
//! trial/iteration index) if two call sites need distinct draws.

use std::hash::{Hash, Hasher};

use crate::{config::NodeId, model::EndorserBlockId};

/// Identifies a distinct random-draw call site. The enum discriminant plus
/// any variant fields are hashed into the context, so two different
/// `DrawSite` values never collide.
// NOTE: add new variants at the END of this enum. Adding variants in the
// middle shifts enum discriminants and breaks `golden_vectors` (and any
// seeded run whose outcomes depend on those draws). Adding at the end
// preserves existing hash outputs for already-used variants.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum DrawSite {
    /// RB lottery at slot boundary.
    RbLottery,
    /// One of the `vote_probability` VRF trials for a given EB vote.
    VoteVrf { eb_id: EndorserBlockId, trial: u16 },
    /// Fisher-Yates swap index `idx` during mempool sampling.
    MempoolSwap { idx: u32 },
    /// Weighted node selection for transaction generation event `tx_idx`.
    TxGenNode { tx_idx: u64 },
    /// Transaction-body random fields for transaction generation event `tx_idx`.
    TxGenBody { tx_idx: u64 },
    /// Whether transaction `tx_idx` introduces an input conflict.
    TxConflict { tx_idx: u64 },
    /// Sampling the frequency-distribution to pick the next TX timestamp.
    TxGenFrequency { tx_idx: u64 },
    /// Should-we-withhold-this-EB-block decision.
    WithholdDecision,
    /// How many TXs to include in a withheld EB.
    WithholdTxCount,
    /// A draw site used by tests. Carries a free-form u64 tag.
    TestRoll { tag: u64 },
    /// One of the `ib_generation_probability` VRF trials at stage-slot
    /// `stage_slot`, trial index `trial` (Leios full variants only).
    IbLottery { stage_slot: u64, trial: u16 },
    /// One of the `eb_generation_probability` VRF trials at pipeline
    /// `pipeline`, trial index `trial` (Leios full / Stracciatella).
    EbLottery { pipeline: u64, trial: u16 },
    /// A vote VRF trial not attached to a specific EB (full Leios votes on
    /// all EBs for a pipeline). `pipeline` is the pipeline we're voting
    /// on, `trial` is the trial index.
    VoteVrfPipeline { pipeline: u64, trial: u16 },
}

/// Stateless pseudo-random oracle: given the fixed `global_seed`, every
/// `draw_*` call is a pure function of its arguments.
#[derive(Clone, Copy, Debug)]
pub struct Rng {
    global_seed: u64,
}

impl Rng {
    pub fn new(global_seed: u64) -> Self {
        Self { global_seed }
    }

    /// Core primitive: return a u64 uniquely determined by
    /// `(global_seed, node, slot, site)`. The same arguments always yield
    /// the same output across runs, platforms, and processes.
    pub fn draw_u64(&self, node: NodeId, slot: u64, site: DrawSite) -> u64 {
        self.draw_u64_with_context(&(node, slot, site))
    }

    /// Hash any `Hash`-implementing context under the global seed. Useful
    /// for contexts that don't fit the `(NodeId, slot, DrawSite)` shape,
    /// e.g. seed-setup draws that aren't associated with a node or slot.
    pub fn draw_u64_with_context<K: Hash>(&self, ctx: &K) -> u64 {
        let mut h = SplitMixHasher::new(self.global_seed);
        ctx.hash(&mut h);
        h.finish()
    }

    /// Uniform in `[0, bound)`. Panics if `bound == 0`.
    pub fn draw_range(&self, node: NodeId, slot: u64, site: DrawSite, bound: u64) -> u64 {
        assert!(bound > 0, "draw_range: bound must be > 0");
        self.draw_u64(node, slot, site) % bound
    }

    /// Uniform in `[0.0, 1.0)`.
    pub fn draw_f64_01(&self, node: NodeId, slot: u64, site: DrawSite) -> f64 {
        // Take the top 53 bits of the u64 so all results are representable
        // in f64 without double-rounding. Divide by 2^53 for [0, 1).
        let bits = self.draw_u64(node, slot, site) >> 11;
        (bits as f64) / (1u64 << 53) as f64
    }

    /// Bernoulli trial: returns `true` with probability `p`. Clamped to
    /// `[0.0, 1.0]`.
    pub fn draw_bool(&self, node: NodeId, slot: u64, site: DrawSite, p: f64) -> bool {
        let p = p.clamp(0.0, 1.0);
        self.draw_f64_01(node, slot, site) < p
    }
}

// ─── portable deterministic hasher ────────────────────────────────────────
//
// `std::collections::hash_map::DefaultHasher` is SipHash-1-3 in current
// rustc but that's an implementation detail and could change. For sim
// determinism we need a hasher whose output is pinned by *our* code. We
// roll one here based on splitmix64, which is tiny, fast, and has
// well-documented mixing properties.
//
// All primitive `write_*` methods are overridden to use `to_le_bytes` so
// results are identical on big-endian and little-endian hosts (current
// std `Hasher::write_u64` uses `to_ne_bytes`).

struct SplitMixHasher {
    state: u64,
}

impl SplitMixHasher {
    fn new(seed: u64) -> Self {
        // Fold the seed with the splitmix constant so seed == 0 isn't a
        // degenerate starting state.
        Self {
            state: seed.wrapping_add(SPLITMIX_GAMMA),
        }
    }

    #[inline]
    fn mix(&mut self, word: u64) {
        // Splitmix-style step: add-rotate-multiply, then xor-shift.
        self.state = self.state.wrapping_add(word).wrapping_mul(SPLITMIX_MUL);
        self.state ^= self.state >> 32;
    }
}

const SPLITMIX_GAMMA: u64 = 0x9E37_79B9_7F4A_7C15;
const SPLITMIX_MUL: u64 = 0xBF58_476D_1CE4_E5B9;
const SPLITMIX_MUL2: u64 = 0x94D0_49BB_1331_11EB;

impl Hasher for SplitMixHasher {
    fn finish(&self) -> u64 {
        // splitmix64 finalizer for avalanche.
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(SPLITMIX_MUL);
        z = (z ^ (z >> 27)).wrapping_mul(SPLITMIX_MUL2);
        z ^ (z >> 31)
    }

    fn write(&mut self, bytes: &[u8]) {
        // Consume 8 bytes at a time; pad the tail with zeros.
        let (chunks, tail) = bytes.as_chunks::<8>();
        for chunk in chunks {
            self.mix(u64::from_le_bytes(*chunk));
        }
        if !tail.is_empty() {
            let mut buf = [0u8; 8];
            buf[..tail.len()].copy_from_slice(tail);
            self.mix(u64::from_le_bytes(buf));
        }
        // Also mix in the length so `[0]` and `[0, 0]` are distinguishable.
        self.mix(bytes.len() as u64);
    }

    // Override primitive writes to pin endianness regardless of target.
    fn write_u8(&mut self, i: u8) {
        self.mix(i as u64);
    }
    fn write_u16(&mut self, i: u16) {
        self.mix(i as u64);
    }
    fn write_u32(&mut self, i: u32) {
        self.mix(i as u64);
    }
    fn write_u64(&mut self, i: u64) {
        self.mix(i);
    }
    fn write_usize(&mut self, i: usize) {
        self.mix(i as u64);
    }
    fn write_i8(&mut self, i: i8) {
        self.mix(i as u64);
    }
    fn write_i16(&mut self, i: i16) {
        self.mix(i as u64);
    }
    fn write_i32(&mut self, i: i32) {
        self.mix(i as u64);
    }
    fn write_i64(&mut self, i: i64) {
        self.mix(i as u64);
    }
    fn write_isize(&mut self, i: isize) {
        self.mix(i as u64);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    fn eb(slot: u64, producer: usize) -> EndorserBlockId {
        EndorserBlockId {
            slot,
            pipeline: 0,
            producer: NodeId::new(producer),
        }
    }

    #[test]
    fn deterministic_given_seed() {
        let rng = Rng::new(12345);
        let a = rng.draw_u64(NodeId::new(7), 42, DrawSite::RbLottery);
        let b = rng.draw_u64(NodeId::new(7), 42, DrawSite::RbLottery);
        assert_eq!(a, b);
    }

    #[test]
    fn different_seeds_produce_different_results() {
        let a = Rng::new(1).draw_u64(NodeId::new(0), 0, DrawSite::RbLottery);
        let b = Rng::new(2).draw_u64(NodeId::new(0), 0, DrawSite::RbLottery);
        assert_ne!(a, b);
    }

    #[test]
    fn different_nodes_slots_sites_produce_different_results() {
        let rng = Rng::new(42);
        let mut seen = HashSet::new();
        // A modest product of contexts — if any pair collides, the set
        // size will be < total pushed. 10*10*5 = 500 distinct inputs.
        let mut total = 0;
        for node in 0..10 {
            for slot in 0..10 {
                for site in [
                    DrawSite::RbLottery,
                    DrawSite::WithholdDecision,
                    DrawSite::WithholdTxCount,
                    DrawSite::MempoolSwap { idx: 3 },
                    DrawSite::TestRoll { tag: 7 },
                ] {
                    let draw = rng.draw_u64(NodeId::new(node), slot, site);
                    seen.insert(draw);
                    total += 1;
                }
            }
        }
        // Not proving uniqueness — but 500 random u64s should have
        // negligible collision probability (~500^2 / 2^64). If we see
        // any collisions here, something is wrong with the hash.
        assert_eq!(seen.len(), total, "unexpected hash collisions");
    }

    #[test]
    fn vote_vrf_trials_produce_different_draws() {
        // The voting code runs 600 VRF trials per EB vote. Each must
        // produce an independent draw; collisions here would collapse
        // 600 Bernoulli trials into correlated draws.
        let rng = Rng::new(999);
        let node = NodeId::new(3);
        let slot = 57;
        let eb_id = eb(57, 3);
        let mut seen = HashSet::new();
        for trial in 0..600u16 {
            let d = rng.draw_u64(node, slot, DrawSite::VoteVrf { eb_id, trial });
            seen.insert(d);
        }
        assert_eq!(seen.len(), 600, "trial-index didn't produce distinct draws");
    }

    #[test]
    fn site_variants_differ_even_at_same_node_slot() {
        // Two call sites sharing (node, slot) but different DrawSite
        // variants must still produce distinct draws — otherwise the
        // protocol's independence assumption between draws is violated.
        let rng = Rng::new(11);
        let n = NodeId::new(5);
        let s = 100;
        let rb = rng.draw_u64(n, s, DrawSite::RbLottery);
        let withhold = rng.draw_u64(n, s, DrawSite::WithholdDecision);
        let mempool = rng.draw_u64(n, s, DrawSite::MempoolSwap { idx: 0 });
        let txgen = rng.draw_u64(n, s, DrawSite::TxGenNode { tx_idx: 0 });
        let vrf = rng.draw_u64(n, s, DrawSite::VoteVrf { eb_id: eb(s, 5), trial: 0 });
        let all = [rb, withhold, mempool, txgen, vrf];
        let unique: HashSet<_> = all.iter().collect();
        assert_eq!(unique.len(), all.len(), "DrawSite variants collided");
    }

    #[test]
    fn draw_range_is_in_range() {
        let rng = Rng::new(7);
        for slot in 0..1000u64 {
            let v = rng.draw_range(NodeId::new(0), slot, DrawSite::RbLottery, 100);
            assert!(v < 100);
        }
    }

    #[test]
    fn draw_f64_01_is_in_01() {
        let rng = Rng::new(8);
        for slot in 0..1000u64 {
            let v = rng.draw_f64_01(NodeId::new(0), slot, DrawSite::RbLottery);
            assert!((0.0..1.0).contains(&v), "out of range: {v}");
        }
    }

    #[test]
    fn draw_bool_approximates_probability() {
        // Bernoulli-trial empirical rate should match p for large N. 10k
        // draws with p=0.3: binomial with mean 3000, stddev ~46. A
        // tolerance of 200 is ~4.3 sigma — false-failure rate <<1/1M.
        let rng = Rng::new(13);
        let p = 0.3;
        let n = 10_000u64;
        let hits: u64 = (0..n)
            .filter(|&slot| rng.draw_bool(NodeId::new(0), slot, DrawSite::RbLottery, p))
            .count() as u64;
        let expected = (n as f64 * p) as i64;
        let diff = (hits as i64 - expected).abs();
        assert!(
            diff < 200,
            "draw_bool rate off by {diff} (got {hits}/{n}, expected ~{expected})"
        );
    }

    #[test]
    fn hash_is_endian_independent() {
        // Check that hashing a u64 via `write_u64` and via `write(&le_bytes)`
        // produce consistent results (i.e. write_u64 uses le_bytes). This
        // guards against the common footgun of `write_u64` falling through
        // to native-endian `write` in Hasher's default impl.
        let mut a = SplitMixHasher::new(0);
        a.write_u64(0x1234_5678_9abc_def0);
        let va = a.finish();
        let mut b = SplitMixHasher::new(0);
        b.write_u64(0x1234_5678_9abc_def0);
        let vb = b.finish();
        assert_eq!(va, vb);
    }

    /// Print all golden-vector values. Temporary helper — run once with
    /// `cargo test -p sim-core --lib rng::tests::print_goldens -- --ignored --nocapture`
    /// and paste the values into the constants below.
    #[test]
    #[ignore]
    fn print_goldens() {
        let rng = Rng::new(0);
        println!(
            "rb_0_0_0 = {}",
            rng.draw_u64(NodeId::new(0), 0, DrawSite::RbLottery)
        );
        println!(
            "rb_0_1_42 = {}",
            rng.draw_u64(NodeId::new(1), 42, DrawSite::RbLottery)
        );
        println!(
            "vote_5_100_0 = {}",
            rng.draw_u64(
                NodeId::new(5),
                100,
                DrawSite::VoteVrf {
                    eb_id: eb(100, 5),
                    trial: 0,
                },
            )
        );
    }

    #[test]
    fn golden_vectors() {
        // Pin a handful of outputs to catch accidental changes to the
        // hash function. If these change, existing seeded runs will no
        // longer reproduce — regenerate with care via `print_goldens`.
        let rng = Rng::new(0);
        assert_eq!(
            rng.draw_u64(NodeId::new(0), 0, DrawSite::RbLottery),
            GOLDEN_RB_LOTTERY_0_0_0,
        );
        assert_eq!(
            rng.draw_u64(NodeId::new(1), 42, DrawSite::RbLottery),
            GOLDEN_RB_LOTTERY_0_1_42,
        );
        assert_eq!(
            rng.draw_u64(
                NodeId::new(5),
                100,
                DrawSite::VoteVrf {
                    eb_id: eb(100, 5),
                    trial: 0
                }
            ),
            GOLDEN_VOTE_VRF_5_100_0,
        );
    }

    const GOLDEN_RB_LOTTERY_0_0_0: u64 = 13_818_903_009_453_492_420;
    const GOLDEN_RB_LOTTERY_0_1_42: u64 = 18_144_849_012_526_513_980;
    const GOLDEN_VOTE_VRF_5_100_0: u64 = 14_971_946_104_597_684_142;
}
