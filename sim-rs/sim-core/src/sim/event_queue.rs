use std::{cmp::Reverse, collections::BinaryHeap, time::Duration};

use crate::clock::{Clock, Timestamp};

use super::SimulationEvent;

pub struct EventQueue {
    clock: Clock,
    scheduled: BinaryHeap<FutureEvent>,
}

impl EventQueue {
    pub fn new(clock: Clock) -> Self {
        Self {
            clock,
            scheduled: BinaryHeap::new(),
        }
    }

    pub fn queue_event(&mut self, event: SimulationEvent, after: Duration) {
        self.scheduled
            .push(FutureEvent(self.clock.now() + after, event));
    }

    pub async fn next_event(&mut self) -> Option<SimulationEvent> {
        let scheduled_event = self.scheduled.peek().cloned()?;
        self.clock.wait_until(scheduled_event.0).await;
        self.scheduled.pop();
        Some(scheduled_event.1)
    }
}

// wrapper struct which holds a SimulationEvent,
// but is ordered by a timestamp (in reverse)
#[derive(Clone)]
struct FutureEvent(Timestamp, SimulationEvent);
impl FutureEvent {
    fn key(&self) -> Reverse<Timestamp> {
        Reverse(self.0)
    }
}

impl PartialEq for FutureEvent {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}
impl Eq for FutureEvent {}
impl PartialOrd for FutureEvent {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for FutureEvent {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}
