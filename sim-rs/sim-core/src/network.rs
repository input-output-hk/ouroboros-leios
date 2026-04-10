use std::{collections::HashMap, fmt::Debug, hash::Hash, sync::Arc, time::Duration};

use anyhow::{Result, bail};
use coordinator::{CrossShardDelivery, EdgeConfig, Message, NetworkCoordinator};
use tokio::sync::mpsc;

use crate::{
    clock::{Clock, ClockBarrier},
    config::NodeId,
};

pub(crate) mod connection;
pub(crate) mod coordinator;

/// Maps a node ID to its shard index.
pub type ShardLookup = Arc<HashMap<NodeId, usize>>;

pub struct Network<TProtocol, TMessage> {
    clock: ClockBarrier,
    coordinator: NetworkCoordinator<TProtocol, TMessage>,
    sink: mpsc::UnboundedSender<Message<TProtocol, TMessage>>,
}

impl<TProtocol: Clone + Eq + Hash, TMessage: Debug> Network<TProtocol, TMessage> {
    pub fn new(clock: Clock) -> Self {
        let (sink, source) = mpsc::unbounded_channel();
        Self {
            clock: clock.barrier(),
            coordinator: NetworkCoordinator::new(source),
            sink,
        }
    }

    pub fn set_edge_policy(
        &mut self,
        from: NodeId,
        to: NodeId,
        latency: Duration,
        bandwidth_bps: Option<u64>,
    ) -> Result<()> {
        self.coordinator.add_edge(EdgeConfig {
            from,
            to,
            latency,
            bandwidth_bps,
        });
        self.coordinator.add_edge(EdgeConfig {
            from: to,
            to: from,
            latency,
            bandwidth_bps,
        });
        Ok(())
    }

    /// Add an incoming cross-shard edge (Connection only, no listen/local_nodes).
    pub fn add_incoming_edge(
        &mut self,
        from: NodeId,
        to: NodeId,
        latency: Duration,
        bandwidth_bps: Option<u64>,
    ) {
        self.coordinator.add_edge(EdgeConfig { from, to, latency, bandwidth_bps });
    }

    /// Set up direct cross-shard routing: this NC sends directly to target NCs.
    pub fn set_cross_shard_routing(
        &mut self,
        targets: Vec<mpsc::UnboundedSender<CrossShardDelivery<TProtocol, TMessage>>>,
        shard_lookup: Arc<HashMap<NodeId, usize>>,
    ) {
        self.coordinator.set_cross_shard_routing(targets, shard_lookup);
    }

    pub fn set_cross_shard_delivery(
        &mut self,
        receiver: mpsc::UnboundedReceiver<CrossShardDelivery<TProtocol, TMessage>>,
    ) {
        self.coordinator.set_cross_shard_delivery(receiver);
    }

    pub fn open(
        &mut self,
        id: NodeId,
    ) -> Result<(NetworkSink<TProtocol, TMessage>, NetworkSource<TMessage>)> {
        let sink = NetworkSink {
            id,
            sink: self.sink.clone(),
        };
        let source = NetworkSource {
            source: self.coordinator.listen(id),
        };
        Ok((sink, source))
    }

    pub async fn run(&mut self) -> Result<()> {
        self.coordinator.run(&mut self.clock).await
    }

}

pub struct NetworkSource<T> {
    source: mpsc::UnboundedReceiver<(NodeId, T)>,
}

impl<T> NetworkSource<T> {
    pub async fn recv(&mut self) -> Option<(NodeId, T)> {
        self.source.recv().await
    }
}

pub struct NetworkSink<TProtocol, TMessage> {
    id: NodeId,
    sink: mpsc::UnboundedSender<Message<TProtocol, TMessage>>,
}

impl<TProtocol, TMessage> NetworkSink<TProtocol, TMessage> {
    pub fn send_to(
        &self,
        to: NodeId,
        bytes: u64,
        protocol: TProtocol,
        message: TMessage,
    ) -> Result<()> {
        if self
            .sink
            .send(Message {
                from: self.id,
                to,
                body: message,
                bytes,
                protocol,
            })
            .is_err()
        {
            bail!("Connection between nodes {} and {} is closed", self.id, to);
        }
        Ok(())
    }
}
