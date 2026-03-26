//! Strict priority scheduler — hardwired priority tiers by protocol ID.
//!
//! Ignores the `TrafficClass` from `ProtocolConfig`. Each protocol ID has a
//! fixed priority from the `priorities` table. Always services the highest-
//! priority (lowest numeric value) protocol first.
//!
//! **Warning**: can starve low-priority protocols indefinitely. Use
//! `PriorityWfq` for fairness within the default class.

use super::{ProtocolId, Scheduler, TrafficClass};

/// Hardwired protocol priority levels (lower = higher priority).
/// Praos protocols (0–4) always outprioritize Leios protocols (5–6).
fn priority_for(id: ProtocolId) -> u8 {
    match id {
        0 => 0,  // Handshake
        2 => 1,  // ChainSync
        3 => 2,  // BlockFetch
        4 => 3,  // TxSubmission
        8 => 4,  // KeepAlive
        19 => 5, // LeiosFetch
        18 => 6, // LeiosNotify
        10 => 7, // PeerSharing
        _ => u8::MAX,
    }
}

/// Strict priority scheduler. Always services the highest-priority protocol
/// (lowest priority value) first. Priority tiers are hardwired by protocol ID.
/// Ties are broken by protocol ID order within the ready set.
#[derive(Debug, Default)]
pub struct StrictPriority {
    /// Registered protocol IDs.
    protocols: Vec<ProtocolId>,
}

impl Scheduler for StrictPriority {
    fn register(&mut self, id: ProtocolId, _tc: TrafficClass) {
        // Ignore traffic class — we use hardwired priorities.
        if !self.protocols.contains(&id) {
            self.protocols.push(id);
        }
    }

    fn next(&mut self, ready: &[ProtocolId]) -> Option<ProtocolId> {
        ready.iter().copied().min_by_key(|id| priority_for(*id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strict_priority_picks_highest() {
        let mut sched = StrictPriority::default();
        sched.register(2, TrafficClass::Priority);
        sched.register(3, TrafficClass::Priority);
        sched.register(4, TrafficClass::Priority);

        // ChainSync (priority 1) beats BlockFetch (2) beats TxSubmission (3).
        assert_eq!(sched.next(&[2, 3, 4]).unwrap(), 2);
        assert_eq!(sched.next(&[3, 4]).unwrap(), 3);
        assert_eq!(sched.next(&[4]).unwrap(), 4);
    }

    #[test]
    fn strict_priority_unknown_protocol() {
        let mut sched = StrictPriority::default();
        sched.register(2, TrafficClass::Priority);
        // Protocol 99 is not in the priority table — gets MAX priority (lowest)
        assert_eq!(sched.next(&[2, 99]).unwrap(), 2);
    }

    #[test]
    fn strict_priority_all_tiers() {
        let mut sched = StrictPriority::default();
        sched.register(0, TrafficClass::Priority);
        sched.register(2, TrafficClass::Priority);
        sched.register(3, TrafficClass::Priority);
        sched.register(4, TrafficClass::Priority);
        sched.register(8, TrafficClass::Priority);
        sched.register(19, TrafficClass::Default(1));
        sched.register(18, TrafficClass::Default(1));
        sched.register(10, TrafficClass::Default(1));

        // All ready: handshake wins (priority 0).
        assert_eq!(sched.next(&[10, 18, 19, 8, 4, 3, 2, 0]).unwrap(), 0);

        // Without handshake: ChainSync wins (priority 1).
        assert_eq!(sched.next(&[10, 18, 19, 8, 4, 3, 2]).unwrap(), 2);

        // Only Leios + PeerSharing: LeiosFetch wins (priority 5).
        assert_eq!(sched.next(&[10, 18, 19]).unwrap(), 19);

        // Only PeerSharing: picks it.
        assert_eq!(sched.next(&[10]).unwrap(), 10);
    }

    #[test]
    fn strict_priority_tiebreak_deterministic() {
        let mut sched = StrictPriority::default();
        sched.register(5, TrafficClass::Priority);
        sched.register(9, TrafficClass::Priority);

        // Both unknown → same priority (MAX). min_by_key picks first in ready-slice order.
        for _ in 0..10 {
            assert_eq!(sched.next(&[5, 9]).unwrap(), 5);
            assert_eq!(sched.next(&[9, 5]).unwrap(), 9);
        }
    }
}
