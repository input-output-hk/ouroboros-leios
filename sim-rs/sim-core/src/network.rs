use std::{collections::HashMap, time::Duration};

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
            .or_insert_with(|| NetworkSource::new());
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
    source: mpsc::UnboundedReceiver<Message<T>>,
    sink: mpsc::UnboundedSender<Message<T>>,
}

impl<T> NetworkSource<T> {
    pub(crate) fn new() -> Self {
        let (sink, source) = mpsc::unbounded_channel();
        Self { source, sink }
    }

    pub async fn recv(&mut self) -> Option<(NodeId, Timestamp, T)> {
        let msg = self.source.recv().await?;
        Some((msg.from, msg.departure + msg.latency, msg.body))
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
            bail!("Connection between nodes {} and {} is closed", self.id, to);
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
