use std::{collections::HashMap, sync::Arc, time::Duration};

use anyhow::Result;
use futures::future::BoxFuture;
use rand::RngCore;
use rand_chacha::{ChaChaRng, rand_core::SeedableRng};
use slot::SlotWitness;
use tokio::{select, sync::mpsc, task::JoinSet};
use tokio_util::sync::CancellationToken;
use tx::TransactionProducer;

use crate::{
    clock::{Clock, ClockCoordinator, Timestamp},
    config::{CpuTimeConfig, LeiosVariant, NodeConfiguration, NodeId, SimConfiguration},
    events::EventTracker,
    model::Transaction,
    network::{Network, ShardLookup},
};

use self::{
    driver::NodeDriver, leios::LeiosNode, linear_leios::LinearLeiosNode,
    stracciatella::StracciatellaLeiosNode,
};

mod cpu;
mod driver;
mod leios;
mod linear_leios;
mod lottery;
mod slot;
mod stracciatella;
#[cfg(test)]
mod tests;
mod tx;

enum NetworkWrapper {
    Leios(Network<MiniProtocol, <LeiosNode as NodeImpl>::Message>),
    Stracciatella(Network<MiniProtocol, <StracciatellaLeiosNode as NodeImpl>::Message>),
    LinearLeios(Network<MiniProtocol, <LinearLeiosNode as NodeImpl>::Message>),
}
impl NetworkWrapper {
    async fn run(&mut self) -> Result<()> {
        match self {
            Self::Leios(network) => network.run().await,
            Self::Stracciatella(network) => network.run().await,
            Self::LinearLeios(network) => network.run().await,
        }
    }

}


enum NodeListWrapper {
    Leios(Vec<NodeDriver<LeiosNode>>),
    Stracciatella(Vec<NodeDriver<StracciatellaLeiosNode>>),
    LinearLeios(Vec<NodeDriver<LinearLeiosNode>>),
}
impl NodeListWrapper {
    fn run_all(&mut self, set: &mut JoinSet<Result<()>>) {
        match self {
            Self::Leios(nodes) => {
                for node in nodes.drain(..) {
                    set.spawn(node.run());
                }
            }
            Self::Stracciatella(nodes) => {
                for node in nodes.drain(..) {
                    set.spawn(node.run());
                }
            }
            Self::LinearLeios(nodes) => {
                for node in nodes.drain(..) {
                    set.spawn(node.run());
                }
            }
        }
    }
}

trait Actor {
    fn run(self: Box<Self>) -> BoxFuture<'static, Result<()>>;
}

struct ActorInitArgs<'a, N: NodeImpl> {
    pub config: Arc<SimConfiguration>,
    pub clock: Clock,
    pub tracker: EventTracker,
    pub nodes: &'a mut [N],
}

fn no_additional_actors<N: NodeImpl>(_args: ActorInitArgs<N>) -> Vec<Box<dyn Actor>> {
    vec![]
}

struct Shard {
    clock_coordinator: ClockCoordinator,
    network: NetworkWrapper,
    tx_producer: TransactionProducer,
}

pub struct Simulation {
    shards: Vec<Shard>,
    slot_witness: SlotWitness,
    nodes: NodeListWrapper,
    actors: Vec<Box<dyn Actor>>,
}

impl Simulation {
    pub async fn new(
        config: SimConfiguration,
        event_sender: mpsc::UnboundedSender<(crate::events::Event, Timestamp)>,
    ) -> Result<Self> {
        let config = Arc::new(config);
        let shard_count = config.shard_count;

        // Build shard lookup: node_id -> shard_index
        let shard_lookup: ShardLookup = crate::sharding::compute_shard_lookup(&config);

        // Create per-shard clock coordinators
        let mut clock_coordinators: Vec<ClockCoordinator> = (0..shard_count)
            .map(|_| ClockCoordinator::new(config.timestamp_resolution))
            .collect();

        let clocks: Vec<Clock> = clock_coordinators.iter().map(|cc| cc.clock()).collect();

        // Create per-shard EventTrackers (all share the same sender channel)
        let trackers: Vec<EventTracker> = clocks
            .iter()
            .map(|clock| EventTracker::new(event_sender.clone(), clock.clone(), &config.nodes))
            .collect();

        let (networks, nodes, actors, tx_producers) = match config.variant {
            LeiosVariant::Linear | LeiosVariant::LinearWithTxReferences => Self::init_sharded(
                &config,
                &trackers,
                &clocks,
                &shard_lookup,
                |nets| nets.into_iter().map(NetworkWrapper::LinearLeios).collect(),
                NodeListWrapper::LinearLeios,
                linear_leios::register_actors,
            )?,
            LeiosVariant::FullWithoutIbs => Self::init_sharded(
                &config,
                &trackers,
                &clocks,
                &shard_lookup,
                |nets| nets.into_iter().map(NetworkWrapper::Stracciatella).collect(),
                NodeListWrapper::Stracciatella,
                no_additional_actors,
            )?,
            _ => Self::init_sharded(
                &config,
                &trackers,
                &clocks,
                &shard_lookup,
                |nets| nets.into_iter().map(NetworkWrapper::Leios).collect(),
                NodeListWrapper::Leios,
                no_additional_actors,
            )?,
        };

        // CMB lookahead: each shard's ceiling = min(peer.time + min_latency[peer→this]).
        // Compute min_latencies from cross-shard edges, clamped to timestamp_resolution.
        if shard_count > 1 {
            let mut min_latencies = vec![vec![Duration::MAX; shard_count]; shard_count];
            for link in &config.links {
                let fs = shard_lookup[&link.nodes.0];
                let ts = shard_lookup[&link.nodes.1];
                if fs != ts {
                    if link.latency < min_latencies[fs][ts] {
                        min_latencies[fs][ts] = link.latency;
                    }
                    if link.latency < min_latencies[ts][fs] {
                        min_latencies[ts][fs] = link.latency;
                    }
                }
            }
            let min_lookahead = config.timestamp_resolution;
            for i in 0..shard_count {
                let peers: Vec<crate::clock::PeerShard> = (0..shard_count)
                    .filter(|&j| j != i)
                    .filter(|&j| min_latencies[j][i] != Duration::MAX)
                    .map(|j| crate::clock::PeerShard {
                        time: clock_coordinators[j].shared_time(),
                        min_latency: min_latencies[j][i].max(min_lookahead),
                        time_advanced: clock_coordinators[j].time_advanced_notify(),
                    })
                    .collect();
                clock_coordinators[i].set_peer_shards(peers);
            }
        }

        // SlotWitness uses shard 0's clock
        let slot_witness = SlotWitness::new(clocks[0].barrier(), trackers[0].clone(), &config);

        let shards: Vec<Shard> = clock_coordinators
            .into_iter()
            .zip(networks)
            .zip(tx_producers)
            .map(|((cc, net), txp)| Shard {
                clock_coordinator: cc,
                network: net,
                tx_producer: txp,
            })
            .collect();

        Ok(Self {
            shards,
            slot_witness,
            nodes,
            actors,
        })
    }

    #[allow(clippy::type_complexity, clippy::too_many_arguments)]
    fn init_sharded<N, NF, NLF, AAF>(
        config: &Arc<SimConfiguration>,
        trackers: &[EventTracker],
        clocks: &[Clock],
        shard_lookup: &ShardLookup,
        network_wrapper_fn: NF,
        node_list_wrapper_fn: NLF,
        additional_actors_fn: AAF,
    ) -> Result<(
        Vec<NetworkWrapper>,
        NodeListWrapper,
        Vec<Box<dyn Actor>>,
        Vec<TransactionProducer>,
    )>
    where
        N: NodeImpl,
        N::Message: Send + 'static,
        NF: FnOnce(Vec<Network<MiniProtocol, N::Message>>) -> Vec<NetworkWrapper>,
        NLF: FnOnce(Vec<NodeDriver<N>>) -> NodeListWrapper,
        AAF: FnOnce(ActorInitArgs<N>) -> Vec<Box<dyn Actor>>,
    {
        let shard_count = clocks.len();
        let mut rng = ChaChaRng::seed_from_u64(config.seed);

        // Create per-shard networks
        let mut networks: Vec<Network<MiniProtocol, N::Message>> = clocks
            .iter()
            .map(|clock| Network::new(clock.clone()))
            .collect();

        // Set up direct NC-to-NC cross-shard routing (bypasses broker for delivery)
        if shard_count > 1 {
            let mut delivery_sinks = Vec::new();
            for network in &mut networks {
                let (tx, rx) = mpsc::unbounded_channel();
                delivery_sinks.push(tx);
                network.set_cross_shard_delivery(rx);
            }
            for network in &mut networks {
                network.set_cross_shard_routing(
                    delivery_sinks.clone(),
                    shard_lookup.clone(),
                );
            }
        }

        // Add edges to per-shard networks
        for link_config in config.links.iter() {
            let from = link_config.nodes.0;
            let to = link_config.nodes.1;
            let from_shard = shard_lookup[&from];
            let to_shard = shard_lookup[&to];

            if from_shard == to_shard {
                // Intra-shard: both directions go to the same shard's network
                networks[from_shard].set_edge_policy(
                    from,
                    to,
                    link_config.latency,
                    link_config.bandwidth_bps,
                )?;
            } else {
                // Cross-shard: add incoming connections to each target shard's NC
                // so it can handle timing locally when messages are routed.
                networks[to_shard].add_incoming_edge(
                    from, to, link_config.latency, link_config.bandwidth_bps,
                );
                networks[from_shard].add_incoming_edge(
                    to, from, link_config.latency, link_config.bandwidth_bps,
                );
            }
        }

        // Create node implementations
        let mut node_impls = vec![];
        for node_config in &config.nodes {
            let shard = shard_lookup[&node_config.id];
            node_impls.push(N::new(
                node_config,
                config.clone(),
                trackers[shard].clone(),
                ChaChaRng::seed_from_u64(rng.next_u64()),
                clocks[shard].clone(),
            ));
        }

        // Additional actors (e.g. linear_leios attackers) use shard 0's clock
        let actor_args = ActorInitArgs {
            config: config.clone(),
            clock: clocks[0].clone(),
            tracker: trackers[0].clone(),
            nodes: &mut node_impls,
        };
        let actors = additional_actors_fn(actor_args);

        // Create node drivers, grouped by shard
        let mut per_shard_tx_sinks: Vec<HashMap<NodeId, mpsc::UnboundedSender<Arc<Transaction>>>> =
            (0..shard_count).map(|_| HashMap::new()).collect();
        let mut all_nodes = vec![];
        for (node_config, node) in config.nodes.iter().zip(node_impls) {
            let id = node_config.id;
            let shard = shard_lookup[&id];
            let (tx_sink, tx_source) = mpsc::unbounded_channel();
            per_shard_tx_sinks[shard].insert(id, tx_sink);
            let driver = NodeDriver::new(
                node,
                node_config,
                config.clone(),
                &mut networks[shard],
                tx_source,
                trackers[shard].clone(),
                clocks[shard].barrier(),
            );
            all_nodes.push(driver);
        }

        // Create per-shard transaction producers
        let tx_producers: Vec<TransactionProducer> = per_shard_tx_sinks
            .into_iter()
            .enumerate()
            .map(|(shard, tx_sinks)| {
                TransactionProducer::new(
                    ChaChaRng::seed_from_u64(rng.next_u64()),
                    clocks[shard].barrier(),
                    tx_sinks,
                    config,
                )
            })
            .collect();

        let networks = network_wrapper_fn(networks);

        Ok((
            networks,
            node_list_wrapper_fn(all_nodes),
            actors,
            tx_producers,
        ))
    }

    /// Run the simulation. Consumes self so shards can be spawned as independent tasks.
    pub async fn run(mut self, token: CancellationToken) -> Result<()> {
        let mut set = JoinSet::new();

        self.nodes.run_all(&mut set);
        for actor in self.actors {
            set.spawn(actor.run());
        }

        if self.shards.len() == 1 {
            // Single shard: run everything in one task via select! for minimal overhead
            let mut shard = self.shards.pop().unwrap();
            select! {
                biased;
                _ = token.cancelled() => {}
                _ = self.slot_witness.run() => {}
                _ = shard.clock_coordinator.run() => {}
                result = shard.network.run() => { result? }
                result = shard.tx_producer.run() => { result?; }
                result = set.join_next() => { result.unwrap()??; }
            };
        } else {
            // Multi-shard: spawn each shard as its own tokio task (independent LP)
            let mut slot_witness = self.slot_witness;
            let slot_token = token.clone();
            set.spawn(async move {
                select! {
                    _ = slot_token.cancelled() => {}
                    _ = slot_witness.run() => { slot_token.cancel(); }
                }
                Ok(())
            });

            for mut shard in self.shards {
                let shard_token = token.clone();
                set.spawn(async move {
                    select! {
                        _ = shard_token.cancelled() => {}
                        _ = shard.clock_coordinator.run() => {}
                        result = shard.network.run() => { result? }
                        result = shard.tx_producer.run() => { result?; }
                    }
                    Ok(())
                });
            }

            // Wait for tasks — errors during normal operation propagate,
            // but errors after cancellation (e.g. closed channels) are expected.
            while let Some(result) = set.join_next().await {
                match result {
                    Ok(Ok(())) => {}
                    Ok(Err(e)) => {
                        if !token.is_cancelled() {
                            token.cancel();
                            return Err(e);
                        }
                    }
                    Err(e) => {
                        if !token.is_cancelled() {
                            token.cancel();
                            return Err(e.into());
                        }
                    }
                }
            }
        }

        Ok(())
    }
}

trait SimMessage: Clone + std::fmt::Debug {
    fn protocol(&self) -> MiniProtocol;
    fn bytes_size(&self) -> u64;
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum MiniProtocol {
    Tx,
    Block,
    IB,
    EB,
    Vote,
}

trait SimCpuTask {
    fn name(&self) -> String;
    fn extra(&self) -> String;
    fn times(&self, config: &CpuTimeConfig) -> Vec<Duration>;
}

struct EventResult<N: NodeImpl> {
    messages: Vec<(NodeId, N::Message)>,
    tasks: Vec<N::Task>,
    timed_events: Vec<(Timestamp, N::TimedEvent)>,
}

impl<N: NodeImpl> Default for EventResult<N> {
    fn default() -> Self {
        Self {
            messages: vec![],
            tasks: vec![],
            timed_events: vec![],
        }
    }
}

impl<N: NodeImpl> EventResult<N> {
    #[cfg(test)]
    pub fn merge(&mut self, mut other: EventResult<N>) {
        self.messages.append(&mut other.messages);
        self.tasks.append(&mut other.tasks);
        self.timed_events.append(&mut other.timed_events);
    }

    pub fn send_to(&mut self, to: NodeId, msg: N::Message) {
        self.messages.push((to, msg));
    }

    pub fn schedule_cpu_task(&mut self, task: N::Task) {
        self.tasks.push(task);
    }

    pub fn schedule_event(&mut self, time: Timestamp, event: N::TimedEvent) {
        self.timed_events.push((time, event));
    }
}

trait NodeImpl: Sized {
    type Message: SimMessage;
    type Task: SimCpuTask;
    type TimedEvent;
    type CustomEvent;

    fn new(
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        tracker: EventTracker,
        rng: ChaChaRng,
        clock: Clock,
    ) -> Self;

    fn custom_event_source(&mut self) -> Option<mpsc::UnboundedReceiver<Self::CustomEvent>> {
        None
    }

    fn handle_new_slot(&mut self, slot: u64) -> EventResult<Self>;
    fn handle_new_tx(&mut self, tx: Arc<Transaction>) -> EventResult<Self>;
    fn handle_message(&mut self, from: NodeId, msg: Self::Message) -> EventResult<Self>;
    fn handle_cpu_task(&mut self, task: Self::Task) -> EventResult<Self>;
    fn handle_timed_event(&mut self, event: Self::TimedEvent) -> EventResult<Self> {
        let _ = event;
        EventResult::default()
    }
    fn handle_custom_event(&mut self, event: Self::CustomEvent) -> EventResult<Self> {
        let _ = event;
        EventResult::default()
    }
}
