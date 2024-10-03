use tokio::sync::mpsc;
use tracing::warn;

use crate::config::PoolId;

pub enum Event {
    Slot {
        number: u64,
        publisher: Option<PoolId>,
        conflicts: Vec<PoolId>,
    },
}

#[derive(Clone)]
pub struct EventTracker(mpsc::UnboundedSender<Event>);

impl EventTracker {
    pub fn new(inner: mpsc::UnboundedSender<Event>) -> Self {
        Self(inner)
    }

    pub fn track_slot(&self, number: u64, publisher: Option<PoolId>, conflicts: Vec<PoolId>) {
        self.send(Event::Slot {
            number,
            publisher,
            conflicts,
        });
    }

    fn send(&self, event: Event) {
        if self.0.send(event).is_err() {
            warn!("tried sending event after aggregator finished");
        }
    }
}
