use std::{cmp::Reverse, collections::BinaryHeap, pin::Pin, time::Duration};

use async_stream::stream;
use futures::{stream::select_all, Stream, StreamExt};
use tokio::select;

use crate::{
    clock::{Clock, Timestamp},
    config::NodeId,
    network::NetworkSource,
};

use super::{SimulationEvent, SimulationMessage};

pub struct EventQueue {
    clock: Clock,
    scheduled: BinaryHeap<FutureEvent>,
    msg_source: Pin<Box<dyn Stream<Item = SimulationEvent>>>,
}

impl EventQueue {
    pub fn new(clock: Clock, msg_sources: Vec<(NodeId, NetworkSource<SimulationMessage>)>) -> Self {
        Self {
            clock,
            scheduled: BinaryHeap::new(),
            msg_source: Box::pin(stream_incoming_messages(msg_sources)),
        }
    }

    pub fn queue_event(&mut self, event: SimulationEvent, after: Duration) {
        self.scheduled
            .push(FutureEvent(self.clock.now() + after, event));
    }

    pub async fn next_event(&mut self) -> Option<SimulationEvent> {
        let scheduled_event = self.scheduled.peek().cloned();
        let clock = self.clock.clone();

        let next_scheduled_event = async move {
            let FutureEvent(timestamp, event) = scheduled_event?;
            clock.wait_until(timestamp).await;
            Some(event)
        };
        let next_network_event = &mut self.msg_source.next();

        select! {
            biased; // always poll the "next scheduled event" future first
            Some(event) = next_scheduled_event => {
                self.scheduled.pop();
                Some(event)
            }
            Some(event) = next_network_event => Some(event),
            else => None
        }
    }
}

fn stream_incoming_messages(
    msg_sources: Vec<(NodeId, NetworkSource<SimulationMessage>)>,
) -> impl Stream<Item = SimulationEvent> {
    select_all(msg_sources.into_iter().map(|(to, mut source)| {
        let stream = stream! {
            while let Some((from, msg)) = source.recv().await {
                yield SimulationEvent::NetworkMessage { from, to, msg }
            }
        };
        Box::pin(stream)
    }))
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
