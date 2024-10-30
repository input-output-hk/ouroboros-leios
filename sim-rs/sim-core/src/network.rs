use std::{
    collections::{HashMap, VecDeque},
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
    node_messages: HashMap<NodeId, VecDeque<Message<T>>>,
    node_next_events: HashMap<NodeId, Timestamp>,
    source: mpsc::UnboundedReceiver<Message<T>>,
    sink: mpsc::UnboundedSender<Message<T>>,
    clock: Clock,
}

impl<T> NetworkSource<T> {
    fn new(clock: Clock) -> Self {
        let (sink, source) = mpsc::unbounded_channel();
        Self {
            node_messages: HashMap::new(),
            node_next_events: HashMap::new(),
            source,
            sink,
            clock,
        }
    }

    pub async fn recv(&mut self) -> Option<(NodeId, T)> {
        // Pull in any messages we were waiting on
        while let Ok(message) = self.source.try_recv() {
            self.schedule_message(message);
        }

        // If we don't have anything pending yet, block until we do
        if self.node_next_events.is_empty() {
            let next = self.source.recv().await?;
            self.schedule_message(next);
        }

        // Now we have a pending message from at least one node. Sleep until the message "should" arrive...
        let (next_from, next_timestamp) = self.node_next_events.iter().min_by_key(|(_, ts)| *ts)?;
        let from = *next_from;
        let timestamp = *next_timestamp;
        self.clock.wait_until(timestamp).await;

        let messages = self.node_messages.get_mut(&from)?;
        let msg = messages.pop_front()?;

        // Track when the next message from this sender will arrive
        if let Some(next) = messages.front() {
            self.node_next_events
                .insert(from, next.departure + next.latency);
        } else {
            self.node_next_events.remove(&from);
        }

        Some((from, msg.body))
    }

    fn schedule_message(&mut self, message: Message<T>) {
        let messages = self.node_messages.entry(message.from).or_default();
        if messages.is_empty() {
            let arrival = message.departure + message.latency;
            self.node_next_events.insert(message.from, arrival);
        }
        messages.push_back(message);
    }
}

pub struct NetworkSink<T> {
    id: NodeId,
    channels: HashMap<NodeId, (mpsc::UnboundedSender<Message<T>>, Duration)>,
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
        if sink
            .send(Message {
                from: self.id,
                departure: self.clock.now(),
                latency: *latency,
                body: msg,
            })
            .is_err()
        {
            bail!("Connection is closed")
        }
        Ok(())
    }
}

struct Message<T> {
    from: NodeId,
    departure: Timestamp,
    latency: Duration,
    body: T,
}
