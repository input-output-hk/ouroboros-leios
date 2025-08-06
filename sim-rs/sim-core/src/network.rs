use std::{fmt::Debug, hash::Hash, time::Duration};

use anyhow::{Result, bail};
use coordinator::{EdgeConfig, Message, NetworkCoordinator};
use tokio::sync::mpsc;

use crate::{
    clock::{Clock, ClockBarrier},
    config::NodeId,
};

mod connection;
mod coordinator;

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

    pub fn shutdown(self) -> Result<()> {
        Ok(())
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
