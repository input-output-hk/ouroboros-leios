use std::{collections::HashMap, sync::Arc, time::Duration};

use anyhow::Result;
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
    network::Network,
    sim::{
        driver::NodeDriver, leios::LeiosNode, linear_leios::LinearLeiosNode,
        stracciatella::StracciatellaLeiosNode,
    },
};

mod cpu;
mod driver;
mod leios;
mod linear_leios;
mod lottery;
mod slot;
mod stracciatella;
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

pub struct Simulation {
    clock_coordinator: ClockCoordinator,
    network: NetworkWrapper,
    tx_producer: TransactionProducer,
    slot_witness: SlotWitness,
    nodes: NodeListWrapper,
}

impl Simulation {
    pub async fn new(
        config: SimConfiguration,
        tracker: EventTracker,
        clock_coordinator: ClockCoordinator,
    ) -> Result<Self> {
        let config = Arc::new(config);
        let clock = clock_coordinator.clock();

        let (network, nodes, tx_producer) = match config.variant {
            LeiosVariant::Linear | LeiosVariant::LinearWithTxReferences => Self::init(
                &config,
                &tracker,
                &clock,
                NetworkWrapper::LinearLeios,
                NodeListWrapper::LinearLeios,
            )?,
            LeiosVariant::FullWithoutIbs => Self::init(
                &config,
                &tracker,
                &clock,
                NetworkWrapper::Stracciatella,
                NodeListWrapper::Stracciatella,
            )?,
            _ => Self::init(
                &config,
                &tracker,
                &clock,
                NetworkWrapper::Leios,
                NodeListWrapper::Leios,
            )?,
        };

        let slot_witness = SlotWitness::new(clock.barrier(), tracker, &config);

        Ok(Self {
            clock_coordinator,
            network,
            tx_producer,
            slot_witness,
            nodes,
        })
    }

    fn init<N, NF, NLF>(
        config: &Arc<SimConfiguration>,
        tracker: &EventTracker,
        clock: &Clock,
        network_wrapper_fn: NF,
        node_list_wrapper_fn: NLF,
    ) -> Result<(NetworkWrapper, NodeListWrapper, TransactionProducer)>
    where
        N: NodeImpl,
        NF: FnOnce(Network<MiniProtocol, N::Message>) -> NetworkWrapper,
        NLF: FnOnce(Vec<NodeDriver<N>>) -> NodeListWrapper,
    {
        let mut rng = ChaChaRng::seed_from_u64(config.seed);
        let mut node_tx_sinks = HashMap::new();

        let mut network = Network::new(clock.clone());
        for link_config in config.links.iter() {
            network.set_edge_policy(
                link_config.nodes.0,
                link_config.nodes.1,
                link_config.latency,
                link_config.bandwidth_bps,
            )?;
        }
        let mut nodes = vec![];
        for node_config in &config.nodes {
            let id = node_config.id;
            let (tx_sink, tx_source) = mpsc::unbounded_channel();
            node_tx_sinks.insert(id, tx_sink);
            let leios = N::new(
                node_config,
                config.clone(),
                tracker.clone(),
                ChaChaRng::seed_from_u64(rng.next_u64()),
                clock.clone(),
            );
            let driver = NodeDriver::new(
                leios,
                node_config,
                config.clone(),
                &mut network,
                tx_source,
                tracker.clone(),
                clock.barrier(),
            );
            nodes.push(driver);
        }

        let tx_producer = TransactionProducer::new(
            ChaChaRng::seed_from_u64(rng.next_u64()),
            clock.barrier(),
            node_tx_sinks,
            config,
        );
        Ok((
            network_wrapper_fn(network),
            node_list_wrapper_fn(nodes),
            tx_producer,
        ))
    }

    // Run the simulation indefinitely.
    pub async fn run(&mut self, token: CancellationToken) -> Result<()> {
        let mut set = JoinSet::new();

        self.nodes.run_all(&mut set);

        select! {
            biased;
            _ = token.cancelled() => {}
            _ = self.slot_witness.run() => {}
            _ = self.clock_coordinator.run() => {}
            result = self.network.run() => {
                result?
            }
            result = self.tx_producer.run() => {
                result?;
            }
            result = set.join_next() => {
                result.unwrap()??;
            }
        };

        Ok(())
    }

    pub fn shutdown(self) -> Result<()> {
        self.network.shutdown()
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

    fn new(
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        tracker: EventTracker,
        rng: ChaChaRng,
        clock: Clock,
    ) -> Self;

    fn handle_new_slot(&mut self, slot: u64) -> EventResult<Self>;
    fn handle_new_tx(&mut self, tx: Arc<Transaction>) -> EventResult<Self>;
    fn handle_message(&mut self, from: NodeId, msg: Self::Message) -> EventResult<Self>;
    fn handle_cpu_task(&mut self, task: Self::Task) -> EventResult<Self>;
    fn handle_timed_event(&mut self, event: Self::TimedEvent) -> EventResult<Self> {
        let _ = event;
        EventResult::default()
    }
}
