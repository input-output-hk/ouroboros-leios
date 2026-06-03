//! `DeepReorg` — deliberately triggers a deep self-reorg on a producing
//! node.  Every `every_slots` slots it asks the I/O wrapper to roll the
//! adopted chain back `depth` blocks (via
//! [`crate::praos::PraosState::force_rollback`]) and fork, so downstream
//! followers must recover from a deep `RollBackward` that orphans their
//! adopted tip.  Not an honest behaviour — a chain-chaos / resilience
//! testing tool (and the harness for the deep-rollback recovery work).

use crate::behaviour::Behaviour;

#[derive(Debug, Clone)]
pub struct DeepReorg {
    /// Fire a reorg whenever `slot % every_slots == 0` (clamped to >= 1).
    every_slots: u64,
    /// How many blocks to roll the adopted chain back each time.
    depth: u64,
    /// Last slot a reorg fired, so a slot ticked more than once doesn't
    /// fire twice.  Starts at `u64::MAX` (no slot has fired).
    last_fired: u64,
}

impl DeepReorg {
    pub fn new(every_slots: u64, depth: u64) -> Self {
        Self {
            every_slots: every_slots.max(1),
            depth,
            last_fired: u64::MAX,
        }
    }
}

impl Behaviour for DeepReorg {
    fn name(&self) -> &'static str {
        "deep-reorg"
    }

    fn praos_reorg(&mut self, slot: u64) -> Option<u64> {
        if self.depth == 0 || slot == 0 {
            return None;
        }
        if slot % self.every_slots == 0 && slot != self.last_fired {
            self.last_fired = slot;
            return Some(self.depth);
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fires_every_n_slots_once_each() {
        let mut b = DeepReorg::new(10, 40);
        assert_eq!(b.praos_reorg(0), None); // genesis never fires
        assert_eq!(b.praos_reorg(9), None);
        assert_eq!(b.praos_reorg(10), Some(40));
        assert_eq!(b.praos_reorg(10), None, "same slot doesn't re-fire");
        assert_eq!(b.praos_reorg(11), None);
        assert_eq!(b.praos_reorg(20), Some(40));
    }

    #[test]
    fn zero_depth_is_inert() {
        let mut b = DeepReorg::new(10, 0);
        assert_eq!(b.praos_reorg(10), None);
        assert_eq!(b.praos_reorg(20), None);
    }
}
