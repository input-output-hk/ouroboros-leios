use std::{
    collections::{BinaryHeap, HashMap},
    time::Duration,
};

use anyhow::{bail, Result};
use netsim_async::EdgePolicy;
use tokio::sync::mpsc;

use crate::{
    clock::{Clock, Timestamp},
    config::NodeId,
};

pub struct Network<T> {
    sources: HashMap<NodeId, NetworkSource<T>>,
    sinks: HashMap<NodeId, NetworkSink<T>>,
    clock: Clock,
}

impl<T> Network<T> {
    pub fn new(clock: Clock) -> Self {
        Self {
            sources: HashMap::new(),
            sinks: HashMap::new(),
            clock,
        }
    }

    pub fn set_edge_policy(&mut self, from: NodeId, to: NodeId, policy: EdgePolicy) -> Result<()> {
        self.add_edge(from, to, policy.latency.to_duration());
        self.add_edge(to, from, policy.latency.to_duration());
        Ok(())
    }

    fn add_edge(&mut self, from: NodeId, to: NodeId, latency: Duration) {
        let to_source = self
            .sources
            .entry(to)
            .or_insert_with(|| NetworkSource::new(self.clock.clone()));
        let from_sink = self
            .sinks
            .entry(from)
            .or_insert_with(|| NetworkSink::new(from, self.clock.clone()));
        from_sink
            .channels
            .insert(to, (to_source.sink.clone(), latency));
    }

    pub fn open(&mut self, node_id: NodeId) -> Result<(NetworkSink<T>, NetworkSource<T>)> {
        let Some(sink) = self.sinks.remove(&node_id) else {
            bail!("Node has no edges")
        };
        let Some(source) = self.sources.remove(&node_id) else {
            bail!("Node has no edges")
        };
        Ok((sink, source))
    }

    pub fn shutdown(self) -> Result<()> {
        Ok(())
    }
}

pub struct NetworkSource<T> {
    messages: BinaryHeap<PendingMessage<T>>,
    source: mpsc::UnboundedReceiver<PendingMessage<T>>,
    sink: mpsc::UnboundedSender<PendingMessage<T>>,
    clock: Clock,
}

impl<T> NetworkSource<T> {
    fn new(clock: Clock) -> Self {
        let (sink, source) = mpsc::unbounded_channel();
        Self {
            messages: BinaryHeap::new(),
            source,
            sink,
            clock,
        }
    }
    pub async fn recv(&mut self) -> Option<(NodeId, T)> {
        while let Ok(pending) = self.source.try_recv() {
            self.messages.push(pending);
        }
        if self.messages.is_empty() {
            let next = self.source.recv().await?;
            self.messages.push(next);
        }
        let next = self.messages.peek()?;
        self.clock.wait_until(next.arrival).await;
        let message = self.messages.pop()?;
        Some((message.from, message.body))
    }
}

pub struct NetworkSink<T> {
    id: NodeId,
    channels: HashMap<NodeId, (mpsc::UnboundedSender<PendingMessage<T>>, Duration)>,
    clock: Clock,
}

impl<T> NetworkSink<T> {
    fn new(id: NodeId, clock: Clock) -> Self {
        Self {
            id,
            channels: HashMap::new(),
            clock,
        }
    }
    pub fn send_to(&self, to: NodeId, msg: T) -> Result<()> {
        let Some((sink, latency)) = self.channels.get(&to) else {
            bail!("Invalid connection")
        };
        let arrival = self.clock.now() + *latency;
        if sink
            .send(PendingMessage {
                from: self.id,
                arrival,
                body: msg,
            })
            .is_err()
        {
            bail!("Connection is closed")
        }
        Ok(())
    }
}

struct PendingMessage<T> {
    from: NodeId,
    arrival: Timestamp,
    body: T,
}

impl<T> PartialEq for PendingMessage<T> {
    fn eq(&self, other: &Self) -> bool {
        self.arrival.eq(&other.arrival)
    }
}

impl<T> Eq for PendingMessage<T> {}

impl<T> PartialOrd for PendingMessage<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for PendingMessage<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.arrival.cmp(&self.arrival)
    }
}
