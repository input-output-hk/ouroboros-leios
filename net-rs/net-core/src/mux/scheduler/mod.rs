//! Mux egress scheduling strategies.
//!
//! The scheduler decides which protocol's queued data to transmit next. This
//! is where QoS policy lives — Praos protocols can be prioritized over Leios.
//!
//! Three implementations:
//! - `RoundRobin` — simple round-robin, ignores traffic class (testing)
//! - `StrictPriority` — hardwired priority tiers by protocol ID (can starve)
//! - `PriorityWfq` — Priority class (absolute) + Default class (message-based WFQ)

mod priority_wfq;
mod round_robin;
mod strict_priority;

pub use priority_wfq::PriorityWfq;
pub use round_robin::RoundRobin;
pub use strict_priority::StrictPriority;

use super::ProtocolId;

/// Traffic class assignment for a protocol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrafficClass {
    /// Absolute priority — always serviced first.
    Priority,
    /// Weighted fair queuing with the given weight (>= 1).
    Default(u16),
}

/// A scheduler picks the next protocol to service from those with data ready.
pub trait Scheduler: Send + 'static {
    /// Register a protocol with its traffic class.
    fn register(&mut self, id: ProtocolId, tc: TrafficClass);

    /// Given a set of protocol IDs that have data ready to send, pick the next
    /// one to service. Returns `None` if `ready` is empty.
    fn next(&mut self, ready: &[ProtocolId]) -> Option<ProtocolId>;
}

/// Which scheduler implementation to use. Stored in config, cloned per connection.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum SchedulerType {
    RoundRobin,
    StrictPriority,
    #[default]
    PriorityWfq,
}

/// Type-erased scheduler wrapping all three implementations.
pub enum AnyScheduler {
    RoundRobin(RoundRobin),
    StrictPriority(StrictPriority),
    PriorityWfq(PriorityWfq),
}

impl AnyScheduler {
    /// Create from a `SchedulerType`.
    pub fn from_type(st: SchedulerType) -> Self {
        match st {
            SchedulerType::RoundRobin => Self::RoundRobin(round_robin::RoundRobin::default()),
            SchedulerType::StrictPriority => {
                Self::StrictPriority(strict_priority::StrictPriority::default())
            }
            SchedulerType::PriorityWfq => {
                Self::PriorityWfq(priority_wfq::PriorityWfq::default())
            }
        }
    }
}

impl Default for AnyScheduler {
    fn default() -> Self {
        Self::from_type(SchedulerType::default())
    }
}

impl Scheduler for AnyScheduler {
    fn register(&mut self, id: ProtocolId, tc: TrafficClass) {
        match self {
            Self::RoundRobin(s) => s.register(id, tc),
            Self::StrictPriority(s) => s.register(id, tc),
            Self::PriorityWfq(s) => s.register(id, tc),
        }
    }

    fn next(&mut self, ready: &[ProtocolId]) -> Option<ProtocolId> {
        match self {
            Self::RoundRobin(s) => s.next(ready),
            Self::StrictPriority(s) => s.next(ready),
            Self::PriorityWfq(s) => s.next(ready),
        }
    }
}
