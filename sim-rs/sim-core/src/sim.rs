use std::{collections::HashMap, sync::Arc, time::Duration};

use anyhow::Result;
use rand::RngCore;
use rand_chacha::{ChaChaRng, rand_core::SeedableRng};
use slot::SlotWitness;
use tokio::{select, sync::mpsc, task::JoinSet};
use tokio_util::sync::CancellationToken;
use tx::TransactionProducer;

use crate::{
    clock::ClockCoordinator,
    config::{CpuTimeConfig, NodeId, SimConfiguration},
    events::EventTracker,
    model::Transaction,
    network::Network,
    sim::{driver::NodeDriver, leios::LeiosNode},
};

mod cpu;
mod driver;
mod leios;
mod slot;
mod tx;

enum NetworkWrapper {
    Leios(Network<MiniProtocol, <LeiosNode as NodeImpl>::Message>),
}
impl NetworkWrapper {
    async fn run(&mut self) -> Result<()> {
        match self {
            Self::Leios(network) => network.run().await,
        }
    }

    fn shutdown(self) -> Result<()> {
        match self {
            Self::Leios(network) => network.shutdown(),
        }
    }
}

enum NodeListWrapper {
    Leios(Vec<NodeDriver<LeiosNode>>),
}
impl NodeListWrapper {
    fn run_all(&mut self, set: &mut JoinSet<Result<()>>) {
        match self {
            Self::Leios(nodes) => {
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
        let clock = clock_coordinator.clock();
        let config = Arc::new(config);
        let total_stake = config.nodes.iter().map(|p| p.stake).sum();

        let mut rng = ChaChaRng::seed_from_u64(config.seed);
        let mut node_tx_sinks = HashMap::new();
        // TODO: remove old impl completely
        let (network, nodes) = {
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
                let leios = LeiosNode::new(
                    node_config,
                    config.clone(),
                    total_stake,
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
            (
                NetworkWrapper::Leios(network),
                NodeListWrapper::Leios(nodes),
            )
        };

        let tx_producer = TransactionProducer::new(
            ChaChaRng::seed_from_u64(rng.next_u64()),
            clock.barrier(),
            node_tx_sinks,
            &config,
        );

        let slot_witness = SlotWitness::new(clock.barrier(), tracker, &config);

        Ok(Self {
            clock_coordinator,
            network,
            tx_producer,
            slot_witness,
            nodes,
        })
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

struct EventResult<Message: SimMessage, Task: SimCpuTask> {
    messages: Vec<(NodeId, Message)>,
    tasks: Vec<Task>,
}

impl<Message: SimMessage, Task: SimCpuTask> Default for EventResult<Message, Task> {
    fn default() -> Self {
        Self {
            messages: vec![],
            tasks: vec![],
        }
    }
}

impl<Message: SimMessage, Task: SimCpuTask> EventResult<Message, Task> {
    pub fn send_to(&mut self, to: NodeId, msg: Message) {
        self.messages.push((to, msg));
    }

    pub fn schedule_cpu_task(&mut self, task: Task) {
        self.tasks.push(task);
    }
}

trait NodeImpl {
    type Message: SimMessage;
    type Task: SimCpuTask;

    fn handle_new_slot(&mut self, slot: u64) -> EventResult<Self::Message, Self::Task>;
    fn handle_new_tx(&mut self, tx: Arc<Transaction>) -> EventResult<Self::Message, Self::Task>;
    fn handle_message(
        &mut self,
        from: NodeId,
        msg: Self::Message,
    ) -> EventResult<Self::Message, Self::Task>;
    fn handle_cpu_task(&mut self, task: Self::Task) -> EventResult<Self::Message, Self::Task>;
}
