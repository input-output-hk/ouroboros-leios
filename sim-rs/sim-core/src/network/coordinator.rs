use std::{cmp::Reverse, collections::HashMap, fmt::Debug, time::Duration};

use anyhow::Result;
use priority_queue::PriorityQueue;
use tokio::{select, sync::mpsc};

use crate::{
    clock::{ClockBarrier, Timestamp},
    config::NodeId,
};

use super::connection::Connection;

pub struct NetworkCoordinator<T> {
    source: mpsc::UnboundedReceiver<Message<T>>,
    sinks: HashMap<NodeId, mpsc::UnboundedSender<(NodeId, T)>>,
    connections: HashMap<Link, Connection<T>>,
    events: PriorityQueue<Link, Reverse<Timestamp>>,
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

impl<T: Debug> NetworkCoordinator<T> {
    pub fn new(source: mpsc::UnboundedReceiver<Message<T>>) -> Self {
        Self {
            source,
            sinks: HashMap::new(),
            connections: HashMap::new(),
            events: PriorityQueue::new(),
        }
    }

    pub fn listen(&mut self, to: NodeId) -> mpsc::UnboundedReceiver<(NodeId, T)> {
        let (sink, source) = mpsc::unbounded_channel();
        self.sinks.insert(to, sink);
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
            select! {
                () = waiter => {
                    let (link, Reverse(timestamp)) = self.events.pop().unwrap();
                    assert_eq!(clock.now(), timestamp);
                    let connection = self.connections.get_mut(&link).unwrap();
                    let body = connection.recv(timestamp);
                    clock.start_task();
                    let _ = self
                        .sinks
                        .get(&link.to)
                        .unwrap()
                        .send((link.from, body));
                    if let Some(timestamp) = connection.next_arrival_time() {
                        self.events.push(link, Reverse(timestamp));
                    }
                },
                Some(message) = self.source.recv() => {
                    self.schedule_message(message);
                    clock.finish_task();
                }
            }
        }
    }

    fn schedule_message(&mut self, message: Message<T>) {
        let link = Link {
            from: message.from,
            to: message.to,
        };
        let connection = self.connections.get_mut(&link).unwrap();
        connection.send(message.body, message.bytes, message.sent);
        if let Some(timestamp) = connection.next_arrival_time() {
            self.events.push(link, Reverse(timestamp));
        }
    }
}

pub struct Message<T> {
    pub from: NodeId,
    pub to: NodeId,
    pub body: T,
    pub bytes: u64,
    pub sent: Timestamp,
}
