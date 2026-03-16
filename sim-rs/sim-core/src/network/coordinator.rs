use std::{
    cmp::Reverse,
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
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

pub struct NetworkCoordinator<TProtocol, TMessage> {
    source: mpsc::UnboundedReceiver<Message<TProtocol, TMessage>>,
    sinks: HashMap<NodeId, mpsc::UnboundedSender<(NodeId, TMessage)>>,
    connections: HashMap<Link, Connection<TProtocol, TMessage>>,
    events: PriorityQueue<Link, Reverse<Timestamp>>,
    local_nodes: HashSet<NodeId>,
    cross_shard_sink: Option<mpsc::UnboundedSender<CrossShardMessage<TProtocol, TMessage>>>,
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
            cross_shard_sink: None,
        }
    }

    pub fn set_cross_shard_sink(
        &mut self,
        sink: mpsc::UnboundedSender<CrossShardMessage<TProtocol, TMessage>>,
    ) {
        self.cross_shard_sink = Some(sink);
    }

    pub fn listen(&mut self, to: NodeId) -> mpsc::UnboundedReceiver<(NodeId, TMessage)> {
        let (sink, source) = mpsc::unbounded_channel();
        self.sinks.insert(to, sink);
        self.local_nodes.insert(to);
        source
    }

    /// Get a clone of the delivery sink for a node (for cross-shard delivery).
    pub fn node_sink(&self, id: &NodeId) -> Option<mpsc::UnboundedSender<(NodeId, TMessage)>> {
        self.sinks.get(id).cloned()
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
                    } else if let Some(cross_shard) = &self.cross_shard_sink {
                        // Cross-shard: forward to broker with send timestamp
                        let _ = cross_shard.send(CrossShardMessage {
                            send_time: clock.now(),
                            from: message.from,
                            to: message.to,
                            protocol: message.protocol,
                            body: message.body,
                            bytes: message.bytes,
                        });
                    }
                    clock.finish_task();
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

pub struct CrossShardMessage<TProtocol, TMessage> {
    pub send_time: Timestamp,
    pub from: NodeId,
    pub to: NodeId,
    pub protocol: TProtocol,
    pub body: TMessage,
    pub bytes: u64,
}
