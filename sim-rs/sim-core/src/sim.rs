use std::{collections::HashMap, sync::Arc, time::Duration};

use anyhow::Result;
use netsim_async::HasBytesSize;
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
    model::{
        Block, BlockId, EndorserBlock, EndorserBlockId, InputBlock, InputBlockHeader, InputBlockId,
        Transaction, TransactionId, VoteBundle, VoteBundleId,
    },
    network::Network,
    sim::{driver::NodeDriver, leios::LeiosNode},
};

mod cpu;
mod driver;
mod leios;
mod slot;
mod tx;

enum NodeList {
    Leios(Vec<NodeDriver<LeiosNode>>),
}

pub struct Simulation {
    clock_coordinator: ClockCoordinator,
    network: Network<MiniProtocol, SimulationMessage>,
    tx_producer: TransactionProducer,
    slot_witness: SlotWitness,
    nodes: NodeList,
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

        let mut network = Network::new(clock.clone());

        let mut rng = ChaChaRng::seed_from_u64(config.seed);
        let mut node_tx_sinks = HashMap::new();
        for link_config in config.links.iter() {
            network.set_edge_policy(
                link_config.nodes.0,
                link_config.nodes.1,
                link_config.latency,
                link_config.bandwidth_bps,
            )?;
        }

        // TODO: remove old impl completely
        let nodes = {
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
            NodeList::Leios(nodes)
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

        match &mut self.nodes {
            NodeList::Leios(nodes) => {
                for node in nodes.drain(..) {
                    set.spawn(node.run());
                }
            }
        }

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

#[derive(Clone, Debug)]
enum SimulationMessage {
    // tx "propagation"
    AnnounceTx(TransactionId),
    RequestTx(TransactionId),
    Tx(Arc<Transaction>),
    // praos block propagation
    RollForward(BlockId),
    RequestBlock(BlockId),
    Block(Arc<Block>),
    // IB header propagation
    AnnounceIBHeader(InputBlockId),
    RequestIBHeader(InputBlockId),
    IBHeader(InputBlockHeader, bool /* has_body */),
    // IB transmission
    AnnounceIB(InputBlockId),
    RequestIB(InputBlockId),
    IB(Arc<InputBlock>),
    // EB propagation
    AnnounceEB(EndorserBlockId),
    RequestEB(EndorserBlockId),
    EB(Arc<EndorserBlock>),
    // Get out the vote
    AnnounceVotes(VoteBundleId),
    RequestVotes(VoteBundleId),
    Votes(Arc<VoteBundle>),
}

impl HasBytesSize for SimulationMessage {
    fn bytes_size(&self) -> u64 {
        match self {
            Self::AnnounceTx(_) => 8,
            Self::RequestTx(_) => 8,
            Self::Tx(tx) => tx.bytes,

            Self::RollForward(_) => 8,
            Self::RequestBlock(_) => 8,
            Self::Block(block) => block.bytes(),

            Self::AnnounceIBHeader(_) => 8,
            Self::RequestIBHeader(_) => 8,
            Self::IBHeader(header, _) => header.bytes,

            Self::AnnounceIB(_) => 8,
            Self::RequestIB(_) => 8,
            Self::IB(ib) => ib.bytes(),

            Self::AnnounceEB(_) => 8,
            Self::RequestEB(_) => 8,
            Self::EB(eb) => eb.bytes,

            Self::AnnounceVotes(_) => 8,
            Self::RequestVotes(_) => 8,
            Self::Votes(v) => v.bytes,
        }
    }
}

impl SimulationMessage {
    pub fn protocol(&self) -> MiniProtocol {
        match self {
            Self::AnnounceTx(_) => MiniProtocol::Tx,
            Self::RequestTx(_) => MiniProtocol::Tx,
            Self::Tx(_) => MiniProtocol::Tx,

            Self::RollForward(_) => MiniProtocol::Block,
            Self::RequestBlock(_) => MiniProtocol::Block,
            Self::Block(_) => MiniProtocol::Block,

            Self::AnnounceIBHeader(_) => MiniProtocol::IB,
            Self::RequestIBHeader(_) => MiniProtocol::IB,
            Self::IBHeader(_, _) => MiniProtocol::IB,

            Self::AnnounceIB(_) => MiniProtocol::IB,
            Self::RequestIB(_) => MiniProtocol::IB,
            Self::IB(_) => MiniProtocol::IB,

            Self::AnnounceEB(_) => MiniProtocol::EB,
            Self::RequestEB(_) => MiniProtocol::EB,
            Self::EB(_) => MiniProtocol::EB,

            Self::AnnounceVotes(_) => MiniProtocol::Vote,
            Self::RequestVotes(_) => MiniProtocol::Vote,
            Self::Votes(_) => MiniProtocol::Vote,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum MiniProtocol {
    Tx,
    Block,
    IB,
    EB,
    Vote,
}

trait CpuTask {
    fn name(&self) -> String;
    fn extra(&self) -> String;
    fn times(&self, config: &CpuTimeConfig) -> Vec<Duration>;
}

struct EventResult<Task: CpuTask> {
    messages: Vec<(NodeId, SimulationMessage)>,
    tasks: Vec<Task>,
}

impl<Task: CpuTask> Default for EventResult<Task> {
    fn default() -> Self {
        Self {
            messages: vec![],
            tasks: vec![],
        }
    }
}

impl<Task: CpuTask> EventResult<Task> {
    pub fn send_to(&mut self, to: NodeId, msg: SimulationMessage) {
        self.messages.push((to, msg));
    }

    pub fn schedule_cpu_task(&mut self, task: Task) {
        self.tasks.push(task);
    }
}

trait NodeImpl {
    type Task: CpuTask;

    fn handle_new_slot(&mut self, slot: u64) -> EventResult<Self::Task>;
    fn handle_new_tx(&mut self, tx: Arc<Transaction>) -> EventResult<Self::Task>;
    fn handle_message(&mut self, from: NodeId, msg: SimulationMessage) -> EventResult<Self::Task>;
    fn handle_cpu_task(&mut self, task: Self::Task) -> EventResult<Self::Task>;
}
