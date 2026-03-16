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
    network::{CrossShardBroker, Network, ShardHandle, ShardLookup},
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

    fn shutdown(self) -> Result<()> {
        match self {
            Self::Leios(network) => network.shutdown(),
            Self::Stracciatella(network) => network.shutdown(),
            Self::LinearLeios(network) => network.shutdown(),
        }
    }
}

enum BrokerWrapper {
    Leios(CrossShardBroker<MiniProtocol, <LeiosNode as NodeImpl>::Message>),
    Stracciatella(CrossShardBroker<MiniProtocol, <StracciatellaLeiosNode as NodeImpl>::Message>),
    LinearLeios(CrossShardBroker<MiniProtocol, <LinearLeiosNode as NodeImpl>::Message>),
}
impl BrokerWrapper {
    async fn run(&mut self) -> Result<()> {
        match self {
            Self::Leios(broker) => broker.run().await,
            Self::Stracciatella(broker) => broker.run().await,
            Self::LinearLeios(broker) => broker.run().await,
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
    broker: Option<BrokerWrapper>,
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
        let shard_lookup: ShardLookup = Arc::new(
            config
                .nodes
                .iter()
                .map(|n| (n.id, n.id.to_inner() % shard_count))
                .collect(),
        );

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

        let (networks, nodes, actors, tx_producers, broker) = match config.variant {
            LeiosVariant::Linear | LeiosVariant::LinearWithTxReferences => Self::init_sharded(
                &config,
                &trackers,
                &clocks,
                &mut clock_coordinators,
                &shard_lookup,
                |nets| nets.into_iter().map(NetworkWrapper::LinearLeios).collect(),
                NodeListWrapper::LinearLeios,
                BrokerWrapper::LinearLeios,
                linear_leios::register_actors,
            )?,
            LeiosVariant::FullWithoutIbs => Self::init_sharded(
                &config,
                &trackers,
                &clocks,
                &mut clock_coordinators,
                &shard_lookup,
                |nets| nets.into_iter().map(NetworkWrapper::Stracciatella).collect(),
                NodeListWrapper::Stracciatella,
                BrokerWrapper::Stracciatella,
                no_additional_actors,
            )?,
            _ => Self::init_sharded(
                &config,
                &trackers,
                &clocks,
                &mut clock_coordinators,
                &shard_lookup,
                |nets| nets.into_iter().map(NetworkWrapper::Leios).collect(),
                NodeListWrapper::Leios,
                BrokerWrapper::Leios,
                no_additional_actors,
            )?,
        };

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
            broker: if shard_count > 1 { Some(broker) } else { None },
            slot_witness,
            nodes,
            actors,
        })
    }

    #[allow(clippy::type_complexity, clippy::too_many_arguments)]
    fn init_sharded<N, NF, NLF, BF, AAF>(
        config: &Arc<SimConfiguration>,
        trackers: &[EventTracker],
        clocks: &[Clock],
        clock_coordinators: &mut [ClockCoordinator],
        shard_lookup: &ShardLookup,
        network_wrapper_fn: NF,
        node_list_wrapper_fn: NLF,
        broker_wrapper_fn: BF,
        additional_actors_fn: AAF,
    ) -> Result<(
        Vec<NetworkWrapper>,
        NodeListWrapper,
        Vec<Box<dyn Actor>>,
        Vec<TransactionProducer>,
        BrokerWrapper,
    )>
    where
        N: NodeImpl,
        N::Message: Send + 'static,
        NF: FnOnce(Vec<Network<MiniProtocol, N::Message>>) -> Vec<NetworkWrapper>,
        NLF: FnOnce(Vec<NodeDriver<N>>) -> NodeListWrapper,
        BF: FnOnce(CrossShardBroker<MiniProtocol, N::Message>) -> BrokerWrapper,
        AAF: FnOnce(ActorInitArgs<N>) -> Vec<Box<dyn Actor>>,
    {
        let shard_count = clocks.len();
        let mut rng = ChaChaRng::seed_from_u64(config.seed);

        // Create cross-shard message channel
        let (cross_shard_sink, cross_shard_source) = mpsc::unbounded_channel();

        // Create per-shard networks
        let mut networks: Vec<Network<MiniProtocol, N::Message>> = clocks
            .iter()
            .map(|clock| Network::new(clock.clone()))
            .collect();

        // Set cross-shard sink on all networks
        if shard_count > 1 {
            for network in &mut networks {
                network.set_cross_shard_sink(cross_shard_sink.clone());
            }
        }

        // Add intra-shard edges to per-shard networks, cross-shard edges to broker
        let mut broker_edges: Vec<(NodeId, NodeId, Duration, Option<u64>)> = Vec::new();
        for link_config in config.links.iter() {
            let from = link_config.nodes.0;
            let to = link_config.nodes.1;
            let from_shard = shard_lookup[&from];
            let to_shard = shard_lookup[&to];

            if from_shard == to_shard {
                // Both directions go to the same shard's network
                networks[from_shard].set_edge_policy(
                    from,
                    to,
                    link_config.latency,
                    link_config.bandwidth_bps,
                )?;
            } else {
                // Cross-shard: add to each shard's network (for outbound routing)
                // and to the broker (for timing/delivery).
                // Each shard's network needs the edge so it can recognize the target as non-local
                // and forward to the broker. But it doesn't need a Connection for it —
                // the broker handles timing. So we don't add edges to the networks.
                broker_edges.push((from, to, link_config.latency, link_config.bandwidth_bps));
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

        // Create broker with direct node sinks for cross-shard delivery
        let shard_handles: Vec<ShardHandle<N::Message>> = (0..shard_count)
            .map(|i| {
                let mut node_sinks = HashMap::new();
                for node_config in &config.nodes {
                    if shard_lookup[&node_config.id] == i
                        && let Some(sink) = networks[i].node_sink(&node_config.id)
                    {
                        node_sinks.insert(node_config.id, sink);
                    }
                }
                ShardHandle {
                    node_sinks,
                    shard_time: clock_coordinators[i].shared_time(),
                    time_advanced: clock_coordinators[i].time_advanced_notify(),
                    tasks: clocks[i].task_initiator(),
                }
            })
            .collect();

        let mut broker =
            CrossShardBroker::new(cross_shard_source, shard_handles, shard_lookup.clone());
        // Compute min latencies between shards and set up peer shard references
        let mut min_latencies = vec![vec![Duration::MAX; shard_count]; shard_count];
        for (from, to, latency, bandwidth_bps) in &broker_edges {
            broker.add_edge(*from, *to, *latency, *bandwidth_bps);
            broker.add_edge(*to, *from, *latency, *bandwidth_bps);
            let fs = shard_lookup[from];
            let ts = shard_lookup[to];
            if *latency < min_latencies[fs][ts] {
                min_latencies[fs][ts] = *latency;
            }
            if *latency < min_latencies[ts][fs] {
                min_latencies[ts][fs] = *latency;
            }
        }

        // Give each coordinator references to peer shard times + min latencies
        if shard_count > 1 {
            for i in 0..shard_count {
                let peers: Vec<crate::clock::PeerShard> = (0..shard_count)
                    .filter(|&j| j != i)
                    .filter(|&j| min_latencies[j][i] != Duration::MAX)
                    .map(|j| crate::clock::PeerShard {
                        time: clock_coordinators[j].shared_time(),
                        min_latency: min_latencies[j][i],
                        time_advanced: clock_coordinators[j].time_advanced_notify(),
                    })
                    .collect();
                clock_coordinators[i].set_peer_shards(peers);
            }
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
        let broker = broker_wrapper_fn(broker);

        Ok((
            networks,
            node_list_wrapper_fn(all_nodes),
            actors,
            tx_producers,
            broker,
        ))
    }

    // Run the simulation indefinitely.
    pub async fn run(&mut self, token: CancellationToken) -> Result<()> {
        let mut set = JoinSet::new();

        self.nodes.run_all(&mut set);
        for actor in self.actors.drain(..) {
            set.spawn(actor.run());
        }

        // Spawn per-shard tasks
        // We need to run clock coordinators and networks for each shard concurrently.
        // Since we can't move self into multiple futures, we'll use a JoinSet approach.

        // Unfortunately, the clock coordinators and networks borrow &mut self,
        // so we need to restructure. Let's run them all in the select.

        // For now, handle the common single-shard case and multi-shard case separately.
        if self.shards.len() == 1 {
            let shard = &mut self.shards[0];
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
            // Multi-shard: run each shard's coordinator + network + tx_producer concurrently
            let mut shard_futures: Vec<BoxFuture<'_, Result<()>>> = Vec::new();
            for shard in &mut self.shards {
                shard_futures.push(Box::pin(async {
                    select! {
                        _ = shard.clock_coordinator.run() => {}
                        result = shard.network.run() => { result? }
                        result = shard.tx_producer.run() => { result?; }
                    }
                    Ok(())
                }));
            }

            let broker = self.broker.as_mut();

            select! {
                biased;
                _ = token.cancelled() => {}
                _ = self.slot_witness.run() => {}
                result = futures::future::select_all(&mut shard_futures) => {
                    result.0?;
                }
                result = async {
                    if let Some(broker) = broker {
                        broker.run().await?;
                    } else {
                        std::future::pending::<()>().await;
                    }
                    Ok::<(), anyhow::Error>(())
                } => { result? }
                result = set.join_next() => { result.unwrap()??; }
            };
        }

        Ok(())
    }

    pub fn shutdown(self) -> Result<()> {
        for shard in self.shards {
            shard.network.shutdown()?;
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
