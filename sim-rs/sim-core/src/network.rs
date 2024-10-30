use std::time::Duration;

use anyhow::Result;
use netsim_async::{
    Edge, EdgePolicy, HasBytesSize, SimContext, SimId, SimSocketReadHalf, SimSocketWriteHalf,
};

use crate::config::NodeId;

pub struct Network<T: HasBytesSize> {
    context: SimContext<T>,
}

impl<T: HasBytesSize> Network<T> {
    pub fn new(timescale: f64) -> Self {
        let mut config = netsim_async::SimConfiguration::default();
        config.idle_duration =
            Duration::from_secs_f64(config.idle_duration.as_secs_f64() / timescale);
        Self {
            context: SimContext::with_config(config),
        }
    }

    pub fn shutdown(self) -> Result<()> {
        self.context.shutdown()
    }

    pub fn open(&mut self, node_id: NodeId) -> Result<(NetworkSource<T>, NetworkSink<T>)> {
        let socket = self.context.open()?;
        assert_eq!(
            node_id.to_string(),
            socket.id().to_string(),
            "Nodes must be initialized in order"
        );

        let (inner_source, inner_sink) = socket.into_split();
        let source = NetworkSource(inner_source);
        let sink = NetworkSink(inner_sink);
        Ok((source, sink))
    }

    pub fn set_edge_policy(&mut self, from: NodeId, to: NodeId, policy: EdgePolicy) -> Result<()> {
        let from = to_sim_id(from);
        let to = to_sim_id(to);
        let edge = Edge::new((from, to));
        self.context.set_edge_policy(edge, policy)
    }
}

pub struct NetworkSource<T: HasBytesSize>(SimSocketReadHalf<T>);
impl<T: HasBytesSize> NetworkSource<T> {
    pub async fn recv(&mut self) -> Option<(NodeId, T)> {
        let (sim_id, msg) = self.0.recv().await?;
        let node_id = to_node_id(sim_id);
        Some((node_id, msg))
    }
}

pub struct NetworkSink<T: HasBytesSize>(SimSocketWriteHalf<T>);
impl<T: HasBytesSize> NetworkSink<T> {
    pub fn send_to(&self, to: NodeId, msg: T) -> Result<()> {
        let sim_id = to_sim_id(to);
        self.0.send_to(sim_id, msg)
    }
}

fn to_node_id(sim_id: SimId) -> NodeId {
    // SAFETY: these IDs are both wrappers around sequential u64s.
    unsafe { std::mem::transmute(sim_id) }
}

fn to_sim_id(node_id: NodeId) -> SimId {
    // SAFETY: these IDs are both wrappers around sequential u64s.
    unsafe { std::mem::transmute(node_id) }
}
