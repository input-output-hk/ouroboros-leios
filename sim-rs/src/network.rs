use std::sync::{Arc, RwLock};

use anyhow::Result;
use netsim_async::{
    Edge, EdgePolicy, HasBytesSize, SimContext, SimId, SimSocketReadHalf, SimSocketWriteHalf,
};

use crate::config::PoolId;

pub struct Network<T: HasBytesSize> {
    context: SimContext<T>,
    id_lookup: IdLookup,
}

impl<T: HasBytesSize> Network<T> {
    pub fn new() -> Self {
        Self {
            context: SimContext::new(),
            id_lookup: IdLookup::default(),
        }
    }

    pub fn shutdown(self) -> Result<()> {
        self.context.shutdown()
    }

    pub fn open(&mut self, pool_id: PoolId) -> Result<(NetworkSource<T>, NetworkSink<T>)> {
        let socket = self.context.open()?;
        self.id_lookup.add_id_mapping(pool_id, socket.id());

        let (inner_source, inner_sink) = socket.into_split();
        let source = NetworkSource(inner_source, self.id_lookup.clone());
        let sink = NetworkSink(inner_sink, self.id_lookup.clone());
        Ok((source, sink))
    }

    pub fn set_edge_policy(&mut self, from: PoolId, to: PoolId, policy: EdgePolicy) -> Result<()> {
        let from = self.id_lookup.find_sim_id(from);
        let to = self.id_lookup.find_sim_id(to);
        let edge = Edge::new((from, to));
        self.context.set_edge_policy(edge, policy)
    }
}

pub struct NetworkSource<T: HasBytesSize>(SimSocketReadHalf<T>, IdLookup);
impl<T: HasBytesSize> NetworkSource<T> {
    pub async fn recv(&mut self) -> Option<(PoolId, T)> {
        let (sim_id, msg) = self.0.recv().await?;
        let pool_id = self.1.find_pool_id(sim_id);
        Some((pool_id, msg))
    }
}

pub struct NetworkSink<T: HasBytesSize>(SimSocketWriteHalf<T>, IdLookup);
impl<T: HasBytesSize> NetworkSink<T> {
    pub fn send_to(&self, to: PoolId, msg: T) -> Result<()> {
        let sim_id = self.1.find_sim_id(to);
        self.0.send_to(sim_id, msg)
    }
}

// We must map between PoolId (which this code has control over)
// and SimId (an opaque type from the netsim library).
// PoolId is sequentially assigned, so we can look it up by index.
#[derive(Default, Clone)]
struct IdLookup(Arc<RwLock<Vec<SimId>>>);
impl IdLookup {
    fn add_id_mapping(&self, pool_id: PoolId, sim_id: SimId) {
        let mut id_list = self.0.write().expect("id list rwlock poisoned");
        assert_eq!(pool_id.to_inner(), id_list.len());
        id_list.push(sim_id);
    }

    fn find_sim_id(&self, pool_id: PoolId) -> SimId {
        let id_list = self.0.read().expect("id list rwlock poisoned!");
        *id_list
            .get(pool_id.to_inner())
            .expect("unrecognized pool id")
    }

    fn find_pool_id(&self, sim_id: SimId) -> PoolId {
        let id_list = self.0.read().expect("id list rwlock poisoned!");
        let index = id_list
            .iter()
            .position(|&id| id == sim_id)
            .expect("unrecognized sim id");
        PoolId::from_usize(index)
    }
}
