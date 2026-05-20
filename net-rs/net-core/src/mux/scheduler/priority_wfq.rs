//! Two-class scheduler: Priority class (absolute) + Default class (message-based WFQ).
//!
//! Priority-class protocols are always serviced first (round-robin among them).
//! Default-class protocols share remaining bandwidth via weighted fair queuing:
//! each gets message turns proportional to its weight.

use super::{ProtocolId, Scheduler, TrafficClass};

/// Two-class scheduler combining absolute priority with weighted fair queuing.
///
/// - **Priority class**: always serviced first, round-robin among ready.
/// - **Default class**: message-based WFQ using deficit counters. Each protocol
///   gets turns proportional to its weight. Only serviced when no Priority
///   protocol is ready.
#[derive(Debug, Default)]
pub struct PriorityWfq {
    /// Protocols in the Priority class.
    priority_protocols: Vec<ProtocolId>,
    /// Round-robin index for Priority class.
    priority_last: usize,
    /// Protocols in the Default (WFQ) class: (id, weight, deficit).
    default_protocols: Vec<(ProtocolId, u16, i32)>,
}

impl PriorityWfq {
    /// Credit all Default protocols by their weight. Called when all deficits
    /// have been exhausted (all <= 0) to start a new WFQ round.
    fn credit_all(&mut self) {
        for (_, weight, deficit) in &mut self.default_protocols {
            *deficit += *weight as i32;
        }
    }
}

impl Scheduler for PriorityWfq {
    fn register(&mut self, id: ProtocolId, tc: TrafficClass) {
        // Remove any existing entry.
        self.priority_protocols.retain(|p| *p != id);
        self.default_protocols.retain(|(p, _, _)| *p != id);

        match tc {
            TrafficClass::Priority => {
                self.priority_protocols.push(id);
            }
            TrafficClass::Default(weight) => {
                let weight = weight.max(1); // Enforce minimum weight of 1.
                self.default_protocols.push((id, weight, weight as i32));
            }
        }
    }

    fn next(&mut self, ready: &[ProtocolId]) -> Option<ProtocolId> {
        if ready.is_empty() {
            return None;
        }

        // Ring 0: Priority class — round-robin among ready Priority protocols.
        let priority_ready: Vec<ProtocolId> = ready
            .iter()
            .copied()
            .filter(|id| self.priority_protocols.contains(id))
            .collect();

        if !priority_ready.is_empty() {
            self.priority_last = (self.priority_last + 1) % priority_ready.len();
            return Some(priority_ready[self.priority_last]);
        }

        // Ring 1: Default class — WFQ by deficit counter.
        let default_ready: Vec<ProtocolId> = ready
            .iter()
            .copied()
            .filter(|id| self.default_protocols.iter().any(|(p, _, _)| p == id))
            .collect();

        if default_ready.is_empty() {
            return None;
        }

        // If all ready protocols have deficit <= 0, credit everyone to start a new round.
        let all_exhausted = default_ready.iter().all(|id| {
            self.default_protocols
                .iter()
                .find(|(p, _, _)| p == id)
                .map(|(_, _, deficit)| *deficit <= 0)
                .unwrap_or(true)
        });

        if all_exhausted {
            self.credit_all();
        }

        // Pick the ready protocol with the highest deficit.
        let chosen = default_ready
            .iter()
            .copied()
            .max_by_key(|id| {
                self.default_protocols
                    .iter()
                    .find(|(p, _, _)| p == id)
                    .map(|(_, _, deficit)| *deficit)
                    .unwrap_or(0)
            })
            .expect("default_ready is non-empty");

        // Decrement chosen protocol's deficit.
        if let Some((_, _, deficit)) = self
            .default_protocols
            .iter_mut()
            .find(|(p, _, _)| *p == chosen)
        {
            *deficit -= 1;
        }

        Some(chosen)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn priority_always_first() {
        let mut sched = PriorityWfq::default();
        sched.register(2, TrafficClass::Priority);
        sched.register(18, TrafficClass::Default(1));

        // When both ready, Priority always wins.
        for _ in 0..10 {
            assert_eq!(sched.next(&[2, 18]).unwrap(), 2);
        }

        // When only Default ready, it gets serviced.
        assert_eq!(sched.next(&[18]).unwrap(), 18);
    }

    #[test]
    fn priority_round_robin() {
        let mut sched = PriorityWfq::default();
        sched.register(2, TrafficClass::Priority);
        sched.register(3, TrafficClass::Priority);

        let mut counts = [0usize; 2];
        for _ in 0..20 {
            match sched.next(&[2, 3]).unwrap() {
                2 => counts[0] += 1,
                3 => counts[1] += 1,
                _ => panic!("unexpected protocol"),
            }
        }

        // Both should get serviced (round-robin).
        assert_eq!(counts[0], 10);
        assert_eq!(counts[1], 10);
    }

    #[test]
    fn default_equal_weights() {
        let mut sched = PriorityWfq::default();
        sched.register(18, TrafficClass::Default(1));
        sched.register(19, TrafficClass::Default(1));

        let mut counts = [0usize; 2];
        for _ in 0..20 {
            match sched.next(&[18, 19]).unwrap() {
                18 => counts[0] += 1,
                19 => counts[1] += 1,
                _ => panic!("unexpected protocol"),
            }
        }

        // Equal weights → equal turns.
        assert_eq!(counts[0], 10);
        assert_eq!(counts[1], 10);
    }

    #[test]
    fn default_weighted() {
        let mut sched = PriorityWfq::default();
        sched.register(18, TrafficClass::Default(3)); // weight 3
        sched.register(19, TrafficClass::Default(1)); // weight 1

        let mut counts = [0usize; 2];
        for _ in 0..40 {
            match sched.next(&[18, 19]).unwrap() {
                18 => counts[0] += 1,
                19 => counts[1] += 1,
                _ => panic!("unexpected protocol"),
            }
        }

        // weight 3 : weight 1 → 3:1 ratio.
        assert_eq!(counts[0], 30);
        assert_eq!(counts[1], 10);
    }

    #[test]
    fn default_only_when_priority_empty() {
        let mut sched = PriorityWfq::default();
        sched.register(2, TrafficClass::Priority);
        sched.register(18, TrafficClass::Default(1));

        for _ in 0..5 {
            assert_eq!(sched.next(&[2, 18]).unwrap(), 2);
        }

        for _ in 0..5 {
            assert_eq!(sched.next(&[18]).unwrap(), 18);
        }
    }

    #[test]
    fn empty() {
        let mut sched = PriorityWfq::default();
        assert_eq!(sched.next(&[]), None);
    }

    #[test]
    fn mixed_ready_sets() {
        let mut sched = PriorityWfq::default();
        sched.register(2, TrafficClass::Priority);
        sched.register(3, TrafficClass::Priority);
        sched.register(18, TrafficClass::Default(2));
        sched.register(19, TrafficClass::Default(1));

        // All ready: only Priority protocols.
        let pick = sched.next(&[2, 3, 18, 19]).unwrap();
        assert!(pick == 2 || pick == 3);

        // Only Default ready: WFQ takes over.
        let pick = sched.next(&[18, 19]).unwrap();
        assert!(pick == 18 || pick == 19);

        // Unknown protocol in ready set: ignored.
        assert_eq!(sched.next(&[99]), None);
    }

    #[test]
    fn weight_zero_treated_as_one() {
        let mut sched = PriorityWfq::default();
        sched.register(18, TrafficClass::Default(0));
        sched.register(19, TrafficClass::Default(1));

        let mut counts = [0usize; 2];
        for _ in 0..20 {
            match sched.next(&[18, 19]).unwrap() {
                18 => counts[0] += 1,
                19 => counts[1] += 1,
                _ => panic!("unexpected protocol"),
            }
        }

        assert_eq!(counts[0], 10);
        assert_eq!(counts[1], 10);
    }
}
