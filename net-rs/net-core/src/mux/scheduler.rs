//! Mux egress scheduling strategies.
//!
//! The scheduler decides which protocol's queued data to transmit next. This
//! is where QoS policy lives — Praos protocols can be prioritized over Leios.

use super::{Priority, ProtocolId};

/// Standard protocol priority levels (lower = higher priority).
/// Praos protocols (0–4) always outprioritize Leios protocols (5–6).
pub mod priorities {
    /// Handshake: connection setup, runs once.
    pub const HANDSHAKE: u8 = 0;
    /// ChainSync: chain tip tracking, most time-critical.
    pub const CHAINSYNC: u8 = 1;
    /// BlockFetch: block body retrieval.
    pub const BLOCKFETCH: u8 = 2;
    /// TxSubmission: transaction dissemination.
    pub const TXSUBMISSION: u8 = 3;
    /// KeepAlive: Praos connection liveness (small messages).
    pub const KEEPALIVE: u8 = 4;
    /// LeiosFetch: Leios data retrieval (EBs, votes, TXs).
    pub const LEIOS_FETCH: u8 = 5;
    /// LeiosNotify: Leios announcements.
    pub const LEIOS_NOTIFY: u8 = 6;
    /// PeerSharing: peer discovery, lowest priority.
    pub const PEERSHARING: u8 = 7;
}

/// A scheduler picks the next protocol to service from those with data ready.
pub trait Scheduler: Send + 'static {
    /// Register a protocol with its priority level. Lower values = higher priority.
    fn register(&mut self, id: ProtocolId, priority: Priority);

    /// Given a set of protocol IDs that have data ready to send, pick the next
    /// one to service. Returns `None` if `ready` is empty.
    fn next(&mut self, ready: &[ProtocolId]) -> Option<ProtocolId>;
}

/// Simple round-robin scheduler. Ignores priority; services each protocol
/// in turn. This is the Phase 1 default and matches the Haskell implementation's
/// basic behavior.
#[derive(Debug, Default)]
pub struct RoundRobin {
    /// Index of the last protocol serviced, for round-robin cycling.
    last_index: usize,
}

impl Scheduler for RoundRobin {
    fn register(&mut self, _id: ProtocolId, _priority: Priority) {
        // Round-robin doesn't use priority.
    }

    fn next(&mut self, ready: &[ProtocolId]) -> Option<ProtocolId> {
        if ready.is_empty() {
            return None;
        }
        self.last_index = (self.last_index + 1) % ready.len();
        Some(ready[self.last_index])
    }
}

/// Strict priority scheduler. Always services the highest-priority protocol
/// (lowest priority value) first. Ties are broken by protocol ID order within
/// the ready set.
#[derive(Debug, Default)]
pub struct StrictPriority {
    /// Map from protocol ID to its priority level.
    priorities: Vec<(ProtocolId, Priority)>,
}

impl Scheduler for StrictPriority {
    fn register(&mut self, id: ProtocolId, priority: Priority) {
        // Remove any existing entry for this protocol.
        self.priorities.retain(|(p, _)| *p != id);
        self.priorities.push((id, priority));
    }

    fn next(&mut self, ready: &[ProtocolId]) -> Option<ProtocolId> {
        ready.iter().copied().min_by_key(|id| {
            self.priorities
                .iter()
                .find(|(p, _)| *p == *id)
                .map(|(_, prio)| *prio)
                .unwrap_or(u8::MAX)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_robin_cycles() {
        let mut sched = RoundRobin::default();
        let ready = vec![2, 3, 4];

        let a = sched.next(&ready).unwrap();
        let b = sched.next(&ready).unwrap();
        let c = sched.next(&ready).unwrap();
        let d = sched.next(&ready).unwrap();

        // Should cycle through all three, then wrap
        assert_ne!(a, b);
        assert_ne!(b, c);
        assert_eq!(a, d); // wrapped around
    }

    #[test]
    fn round_robin_empty() {
        let mut sched = RoundRobin::default();
        assert_eq!(sched.next(&[]), None);
    }

    #[test]
    fn strict_priority_picks_highest() {
        let mut sched = StrictPriority::default();
        sched.register(2, 10); // ChainSync, high priority
        sched.register(3, 10); // BlockFetch, high priority
        sched.register(4, 20); // TxSubmission, lower priority

        // When all are ready, should pick one of the priority-10 protocols
        let pick = sched.next(&[2, 3, 4]).unwrap();
        assert!(pick == 2 || pick == 3);

        // When only low-priority is ready, picks it
        assert_eq!(sched.next(&[4]).unwrap(), 4);
    }

    #[test]
    fn strict_priority_unknown_protocol() {
        let mut sched = StrictPriority::default();
        sched.register(2, 10);
        // Protocol 99 is not registered — gets MAX priority (lowest)
        assert_eq!(sched.next(&[2, 99]).unwrap(), 2);
    }

    #[test]
    fn strict_priority_all_tiers() {
        use super::priorities;

        let mut sched = StrictPriority::default();
        // Register protocols at each priority tier.
        sched.register(0, priorities::HANDSHAKE);
        sched.register(2, priorities::CHAINSYNC);
        sched.register(3, priorities::BLOCKFETCH);
        sched.register(4, priorities::TXSUBMISSION);
        sched.register(8, priorities::KEEPALIVE);
        sched.register(19, priorities::LEIOS_FETCH);
        sched.register(18, priorities::LEIOS_NOTIFY);
        sched.register(10, priorities::PEERSHARING);

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
        sched.register(5, 10);
        sched.register(9, 10);

        // Same priority — min_by_key picks first in ready-slice order.
        // Call multiple times to verify determinism.
        for _ in 0..10 {
            assert_eq!(sched.next(&[5, 9]).unwrap(), 5);
            assert_eq!(sched.next(&[9, 5]).unwrap(), 9);
        }
    }
}
