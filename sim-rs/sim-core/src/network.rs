use std::sync::{Arc, RwLock};

use anyhow::Result;
use netsim_async::{
    Edge, EdgePolicy, HasBytesSize, SimContext, SimId, SimSocketReadHalf, SimSocketWriteHalf,
};

use crate::config::NodeId;

pub struct Network<T: HasBytesSize> {
    context: SimContext<T>,
    id_lookup: IdLookup,
}

impl<T: HasBytesSize> Network<T> {
    pub fn new(timescale: u32) -> Self {
        let mut config = netsim_async::SimConfiguration::default();
        config.idle_duration /= timescale;
        Self {
            context: SimContext::with_config(config),
            id_lookup: IdLookup::default(),
        }
    }

    pub fn shutdown(self) -> Result<()> {
        self.context.shutdown()
    }

    pub fn open(&mut self, node_id: NodeId) -> Result<(NetworkSource<T>, NetworkSink<T>)> {
        let socket = self.context.open()?;
        self.id_lookup.add_id_mapping(node_id, socket.id());

        let (inner_source, inner_sink) = socket.into_split();
        let source = NetworkSource(inner_source, self.id_lookup.clone());
        let sink = NetworkSink(inner_sink, self.id_lookup.clone());
        Ok((source, sink))
    }

    pub fn set_edge_policy(&mut self, from: NodeId, to: NodeId, policy: EdgePolicy) -> Result<()> {
        let from = self.id_lookup.find_sim_id(from);
        let to = self.id_lookup.find_sim_id(to);
        let edge = Edge::new((from, to));
        self.context.set_edge_policy(edge, policy)
    }
}

pub struct NetworkSource<T: HasBytesSize>(SimSocketReadHalf<T>, IdLookup);
impl<T: HasBytesSize> NetworkSource<T> {
    pub async fn recv(&mut self) -> Option<(NodeId, T)> {
        let (sim_id, msg) = self.0.recv().await?;
        let node_id = self.1.find_node_id(sim_id);
        Some((node_id, msg))
    }
}

pub struct NetworkSink<T: HasBytesSize>(SimSocketWriteHalf<T>, IdLookup);
impl<T: HasBytesSize> NetworkSink<T> {
    pub fn send_to(&self, to: NodeId, msg: T) -> Result<()> {
        let sim_id = self.1.find_sim_id(to);
        self.0.send_to(sim_id, msg)
    }
}

// We must map between NodeId (which this code has control over)
// and SimId (an opaque type from the netsim library).
// NodeId is sequentially assigned, so we can look it up by index.
#[derive(Default, Clone)]
struct IdLookup(Arc<RwLock<Vec<SimId>>>);
impl IdLookup {
    fn add_id_mapping(&self, node_id: NodeId, sim_id: SimId) {
        let mut id_list = self.0.write().expect("id list rwlock poisoned");
        assert_eq!(node_id.to_inner(), id_list.len());
        id_list.push(sim_id);
    }

    fn find_sim_id(&self, node_id: NodeId) -> SimId {
        let id_list = self.0.read().expect("id list rwlock poisoned!");
        *id_list
            .get(node_id.to_inner())
            .expect("unrecognized node id")
    }

    fn find_node_id(&self, sim_id: SimId) -> NodeId {
        let id_list = self.0.read().expect("id list rwlock poisoned!");
        let index = id_list.binary_search(&sim_id).expect("unrecognized sim id");
        NodeId::new(index)
    }
}
