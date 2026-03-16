use std::{
    cmp::Reverse,
    collections::HashMap,
    fmt::Debug,
    hash::Hash,
    sync::Arc,
    time::Duration,
};

use anyhow::Result;
use priority_queue::PriorityQueue;
use tokio::sync::{Notify, mpsc};

use crate::{
    clock::{TaskInitiator, Timestamp},
    clock::timestamp::AtomicTimestamp,
    config::NodeId,
};

use super::connection::Connection;
use super::coordinator::CrossShardMessage;

/// Maps a node ID to its shard index.
pub type ShardLookup = Arc<HashMap<NodeId, usize>>;

/// Per-shard handle that the broker uses to deliver messages and manage timing.
pub struct ShardHandle<TMessage> {
    /// Per-node message sinks for delivering cross-shard messages.
    pub node_sinks: HashMap<NodeId, mpsc::UnboundedSender<(NodeId, TMessage)>>,
    /// This shard's current time (readable atomically).
    pub shard_time: Arc<AtomicTimestamp>,
    /// Notified when this shard's clock advances time.
    pub time_advanced: Arc<Notify>,
    /// Task initiator for start_task on this shard (not a full barrier,
    /// so it doesn't register as a waiter in the clock coordinator).
    pub tasks: TaskInitiator,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Link {
    from: NodeId,
    to: NodeId,
}

/// Handles cross-shard message delivery with proper timing.
pub struct CrossShardBroker<TProtocol, TMessage> {
    source: mpsc::UnboundedReceiver<CrossShardMessage<TProtocol, TMessage>>,
    shard_handles: Vec<ShardHandle<TMessage>>,
    shard_lookup: ShardLookup,
    connections: HashMap<Link, Connection<TProtocol, TMessage>>,
    pending: PriorityQueue<Link, Reverse<Timestamp>>,
    /// min_latencies[from_shard][to_shard] = minimum link latency
    min_latencies: Vec<Vec<Duration>>,
}

impl<TProtocol: Clone + Eq + Hash, TMessage: Debug> CrossShardBroker<TProtocol, TMessage> {
    pub fn new(
        source: mpsc::UnboundedReceiver<CrossShardMessage<TProtocol, TMessage>>,
        shard_handles: Vec<ShardHandle<TMessage>>,
        shard_lookup: ShardLookup,
    ) -> Self {
        let shard_count = shard_handles.len();
        Self {
            source,
            shard_handles,
            shard_lookup,
            connections: HashMap::new(),
            pending: PriorityQueue::new(),
            min_latencies: vec![vec![Duration::MAX; shard_count]; shard_count],
        }
    }

    pub fn add_edge(
        &mut self,
        from: NodeId,
        to: NodeId,
        latency: Duration,
        bandwidth_bps: Option<u64>,
    ) {
        let from_shard = self.shard_lookup[&from];
        let to_shard = self.shard_lookup[&to];
        if from_shard != to_shard
            && latency < self.min_latencies[from_shard][to_shard]
        {
            self.min_latencies[from_shard][to_shard] = latency;
        }
        let link = Link { from, to };
        let connection = Connection::new(latency, bandwidth_bps);
        self.connections.insert(link, connection);
    }

    fn deliver_ready_messages(&mut self) {
        while let Some((link, Reverse(arrival_time))) = self.pending.peek() {
            let to_shard = self.shard_lookup[&link.to];
            let shard_time = self.shard_handles[to_shard]
                .shard_time
                .load(std::sync::atomic::Ordering::Acquire);

            if shard_time < *arrival_time {
                break;
            }

            let link = link.clone();
            let arrival_time = *arrival_time;
            self.pending.pop();

            let connection = self.connections.get_mut(&link).unwrap();
            for (body, _ts) in connection.recv_many(arrival_time) {
                let handle = &self.shard_handles[to_shard];
                handle.tasks.start_task();
                if let Some(node_sink) = handle.node_sinks.get(&link.to) {
                    let _ = node_sink.send((link.from, body));
                }
            }
            if let Some(next_time) = connection.next_arrival_time() {
                self.pending.push(link, Reverse(next_time));
            }
        }
    }

    pub async fn run(&mut self) -> Result<()> {
        let shard_time_notifies: Vec<Arc<Notify>> = self.shard_handles
            .iter()
            .map(|h| h.time_advanced.clone())
            .collect();

        loop {
            // Register interest in shard time advancement BEFORE delivering,
            // to avoid missing notifications.
            let shard_notified: Vec<_> = shard_time_notifies
                .iter()
                .map(|n| Box::pin(n.notified()))
                .collect();

            self.deliver_ready_messages();

            tokio::select! {
                msg = self.source.recv() => {
                    match msg {
                        Some(msg) => {
                            let link = Link {
                                from: msg.from,
                                to: msg.to,
                            };
                            let connection = self.connections.get_mut(&link).unwrap();
                            connection.send(msg.body, msg.bytes, msg.protocol, msg.send_time);
                            if let Some(arrival_time) = connection.next_arrival_time() {
                                self.pending.push(link, Reverse(arrival_time));
                            }
                        }
                        None => return Ok(()),
                    }
                }
                // Wake up when any shard advances time, so we can deliver ready messages
                _ = futures::future::select_all(shard_notified), if !self.pending.is_empty() => {}
            }
        }
    }
}
