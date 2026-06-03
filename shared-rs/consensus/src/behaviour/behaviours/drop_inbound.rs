//! `DropInboundPeers` — randomly resets accepted (inbound) peer
//! connections on a serving node, so the remote reconnects and re-runs
//! ChainSync intersection from scratch.  Mimics a relay that RSTs
//! inbound connections; the reconnect-handover trigger for
//! deep-rollback recovery testing (compose with `DeepReorg` so the
//! reconnect re-intersects against a reorged chain).

use crate::behaviour::Behaviour;

#[derive(Debug, Clone)]
pub struct DropInboundPeers {
    seed: u64,
    /// Per-slot probability of resetting inbound peers, clamped to [0,1].
    probability: f64,
}

impl DropInboundPeers {
    pub fn new(seed: u64, probability: f64) -> Self {
        Self {
            seed,
            probability: probability.clamp(0.0, 1.0),
        }
    }
}

impl Behaviour for DropInboundPeers {
    fn name(&self) -> &'static str {
        "drop-inbound-peers"
    }

    fn drop_inbound_peers(&mut self, slot: u64) -> bool {
        if self.probability <= 0.0 || slot == 0 {
            return false;
        }
        // Deterministic per-(seed, slot) draw in [0, 1): replays
        // identically from a seed (no clock / OS entropy).
        let mut h = blake2b_simd::Params::new().hash_length(8).to_state();
        h.update(&self.seed.to_le_bytes());
        h.update(&slot.to_le_bytes());
        let mut buf = [0u8; 8];
        buf.copy_from_slice(&h.finalize().as_bytes()[..8]);
        let draw = (u64::from_le_bytes(buf) as f64) / (u64::MAX as f64);
        draw < self.probability
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn never_drops_at_zero_probability() {
        let mut b = DropInboundPeers::new(42, 0.0);
        assert!(!b.drop_inbound_peers(100));
        assert!(!b.drop_inbound_peers(200));
    }

    #[test]
    fn always_drops_at_probability_one() {
        let mut b = DropInboundPeers::new(42, 1.0);
        assert!(b.drop_inbound_peers(1));
        assert!(b.drop_inbound_peers(2));
        assert!(!b.drop_inbound_peers(0), "genesis never drops");
    }

    #[test]
    fn deterministic_for_a_given_seed_and_slot() {
        let mut a = DropInboundPeers::new(7, 0.5);
        let mut b = DropInboundPeers::new(7, 0.5);
        for slot in 1..50 {
            assert_eq!(a.drop_inbound_peers(slot), b.drop_inbound_peers(slot));
        }
    }
}
