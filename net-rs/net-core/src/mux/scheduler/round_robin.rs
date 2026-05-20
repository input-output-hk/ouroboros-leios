//! Round-robin scheduler — ignores traffic class, services each protocol in turn.

use super::{ProtocolId, Scheduler, TrafficClass};

/// Simple round-robin scheduler. Ignores traffic class; services each protocol
/// in turn. This is the Phase 1 default and matches the Haskell implementation's
/// basic behavior.
#[derive(Debug, Default)]
pub struct RoundRobin {
    /// Index of the last protocol serviced, for round-robin cycling.
    last_index: usize,
}

impl Scheduler for RoundRobin {
    fn register(&mut self, _id: ProtocolId, _tc: TrafficClass) {
        // Round-robin doesn't use traffic class.
    }

    fn next(&mut self, ready: &[ProtocolId]) -> Option<ProtocolId> {
        if ready.is_empty() {
            return None;
        }
        self.last_index = (self.last_index + 1) % ready.len();
        Some(ready[self.last_index])
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
}
