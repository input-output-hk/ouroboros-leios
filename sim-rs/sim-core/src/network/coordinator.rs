use std::{
    cmp::Reverse,
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    sync::Arc,
    time::Duration,
};

use anyhow::Result;
use priority_queue::PriorityQueue;
use tokio::{select, sync::mpsc};

use crate::{
    clock::{ClockBarrier, Timestamp},
    config::NodeId,
};

use super::connection::Connection;

/// Tuple sent directly from source NC to target NC for cross-shard messages.
pub type CrossShardDelivery<TProtocol, TMessage> = (NodeId, NodeId, TProtocol, TMessage, u64, Timestamp);

pub struct NetworkCoordinator<TProtocol, TMessage> {
    source: mpsc::UnboundedReceiver<Message<TProtocol, TMessage>>,
    sinks: HashMap<NodeId, mpsc::UnboundedSender<(NodeId, TMessage)>>,
    connections: HashMap<Link, Connection<TProtocol, TMessage>>,
    events: PriorityQueue<Link, Reverse<Timestamp>>,
    local_nodes: HashSet<NodeId>,
    /// Per-shard delivery sinks for sending cross-shard messages directly to target NCs.
    cross_shard_targets: Vec<mpsc::UnboundedSender<CrossShardDelivery<TProtocol, TMessage>>>,
    shard_lookup: Option<Arc<HashMap<NodeId, usize>>>,
    /// Receives cross-shard messages from other NCs for local timing/delivery.
    cross_shard_delivery: Option<mpsc::UnboundedReceiver<CrossShardDelivery<TProtocol, TMessage>>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Link {
    from: NodeId,
    to: NodeId,
}

pub struct EdgeConfig {
    pub from: NodeId,
    pub to: NodeId,
    pub latency: Duration,
    pub bandwidth_bps: Option<u64>,
}

impl<TProtocol: Clone + Eq + Hash, TMessage: Debug> NetworkCoordinator<TProtocol, TMessage> {
    pub fn new(source: mpsc::UnboundedReceiver<Message<TProtocol, TMessage>>) -> Self {
        Self {
            source,
            sinks: HashMap::new(),
            connections: HashMap::new(),
            events: PriorityQueue::new(),
            local_nodes: HashSet::new(),
            cross_shard_targets: Vec::new(),
            shard_lookup: None,
            cross_shard_delivery: None,
        }
    }

    /// Set up direct cross-shard routing: this NC sends directly to target NCs.
    pub fn set_cross_shard_routing(
        &mut self,
        targets: Vec<mpsc::UnboundedSender<CrossShardDelivery<TProtocol, TMessage>>>,
        shard_lookup: Arc<HashMap<NodeId, usize>>,
    ) {
        self.cross_shard_targets = targets;
        self.shard_lookup = Some(shard_lookup);
    }

    pub fn set_cross_shard_delivery(
        &mut self,
        receiver: mpsc::UnboundedReceiver<CrossShardDelivery<TProtocol, TMessage>>,
    ) {
        self.cross_shard_delivery = Some(receiver);
    }

    pub fn listen(&mut self, to: NodeId) -> mpsc::UnboundedReceiver<(NodeId, TMessage)> {
        let (sink, source) = mpsc::unbounded_channel();
        self.sinks.insert(to, sink);
        self.local_nodes.insert(to);
        source
    }

    pub fn add_edge(&mut self, config: EdgeConfig) {
        let link = Link {
            from: config.from,
            to: config.to,
        };
        let connection = Connection::new(config.latency, config.bandwidth_bps);
        self.connections.insert(link, connection);
    }

    pub async fn run(&mut self, clock: &mut ClockBarrier) -> Result<()> {
        loop {
            let waiter = match self.events.peek() {
                Some((_, Reverse(timestamp))) => clock.wait_until(*timestamp),
                None => clock.wait_forever(),
            };
            let has_delivery = self.cross_shard_delivery.is_some();
            select! {
                () = waiter => {
                    let (link, Reverse(timestamp)) = self.events.pop().unwrap();
                    assert!(clock.now() >= timestamp);
                    let connection = self.connections.get_mut(&link).unwrap();
                    for (body, _) in connection.recv_many(timestamp) {
                        clock.start_task();
                        let _ = self
                            .sinks
                            .get(&link.to)
                            .unwrap()
                            .send((link.from, body));
                    };
                    if let Some(timestamp) = connection.next_arrival_time() {
                        self.events.push(link, Reverse(timestamp));
                    }
                },
                Some(message) = self.source.recv() => {
                    if self.local_nodes.contains(&message.to) {
                        // Intra-shard: handle locally
                        self.schedule_message(message, clock.now());
                    } else if let Some(lookup) = &self.shard_lookup {
                        // Cross-shard: send directly to target NC
                        let target_shard = lookup[&message.to];
                        let _ = self.cross_shard_targets[target_shard].send((
                            message.from, message.to, message.protocol,
                            message.body, message.bytes, clock.now(),
                        ));
                    }
                    clock.finish_task();
                }
                // Receive cross-shard messages from broker — schedule through
                // local Connection for proper timing (synchronized with coordinator).
                Some((from, to, protocol, body, bytes, send_time)) = async {
                    match &mut self.cross_shard_delivery {
                        Some(rx) => rx.recv().await,
                        None => std::future::pending().await,
                    }
                }, if has_delivery => {
                    let link = Link { from, to };
                    if let Some(connection) = self.connections.get_mut(&link) {
                        connection.send(body, bytes, protocol, send_time);
                        if let Some(timestamp) = connection.next_arrival_time() {
                            self.events.push(link, Reverse(timestamp));
                        }
                    }
                }
            }
        }
    }

    fn schedule_message(&mut self, message: Message<TProtocol, TMessage>, now: Timestamp) {
        let link = Link {
            from: message.from,
            to: message.to,
        };
        let connection = self.connections.get_mut(&link).unwrap();
        connection.send(message.body, message.bytes, message.protocol, now);
        if let Some(timestamp) = connection.next_arrival_time() {
            self.events.push(link, Reverse(timestamp));
        }
    }
}

pub struct Message<TProtocol, TMessage> {
    pub from: NodeId,
    pub to: NodeId,
    pub protocol: TProtocol,
    pub body: TMessage,
    pub bytes: u64,
}

