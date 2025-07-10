#![expect(unused)] // TODO: get rid of this
use std::{sync::Arc, time::Duration};

use rand_chacha::ChaChaRng;

use crate::{
    clock::Clock,
    config::{CpuTimeConfig, NodeConfiguration, NodeId, SimConfiguration},
    events::EventTracker,
    model::{Transaction, TransactionId},
    sim::{MiniProtocol, NodeImpl, SimCpuTask, SimMessage},
};

#[derive(Clone, Debug)]
pub enum Message {
    AnnounceTx(TransactionId),
    RequestTx(TransactionId),
    Tx(Arc<Transaction>),
}

impl SimMessage for Message {
    fn protocol(&self) -> MiniProtocol {
        match self {
            Self::AnnounceTx(_) => MiniProtocol::Tx,
            Self::RequestTx(_) => MiniProtocol::Tx,
            Self::Tx(_) => MiniProtocol::Tx,
        }
    }

    fn bytes_size(&self) -> u64 {
        match self {
            Self::AnnounceTx(_) => 8,
            Self::RequestTx(_) => 8,
            Self::Tx(tx) => tx.bytes,
        }
    }
}

pub enum CpuTask {
    /// A transaction has been received and validated, and is ready to propagate
    TransactionValidated(NodeId, Arc<Transaction>),
}

impl SimCpuTask for CpuTask {
    fn name(&self) -> String {
        match self {
            Self::TransactionValidated(_, _) => "ValTX",
        }
        .to_string()
    }

    fn extra(&self) -> String {
        match self {
            Self::TransactionValidated(_, _) => "".to_string(),
        }
    }

    fn times(&self, config: &CpuTimeConfig) -> Vec<Duration> {
        match self {
            Self::TransactionValidated(_, _) => vec![config.tx_validation],
        }
    }
}

pub struct LinearLeiosNode {
    queued: EventResult,
}

type EventResult = super::EventResult<Message, CpuTask>;

impl NodeImpl for LinearLeiosNode {
    type Message = Message;
    type Task = CpuTask;

    fn new(
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        tracker: EventTracker,
        rng: ChaChaRng,
        clock: Clock,
    ) -> Self {
        Self {
            queued: EventResult::default(),
        }
    }

    fn handle_new_slot(&mut self, _slot: u64) -> EventResult {
        std::mem::take(&mut self.queued)
    }

    fn handle_new_tx(&mut self, _tx: Arc<Transaction>) -> EventResult {
        // TODO: propagate TX
        std::mem::take(&mut self.queued)
    }

    fn handle_message(&mut self, _from: NodeId, _msg: Self::Message) -> EventResult {
        // TODO: propagate TX
        std::mem::take(&mut self.queued)
    }

    fn handle_cpu_task(&mut self, _task: Self::Task) -> EventResult {
        // TODO: propagate TX
        std::mem::take(&mut self.queued)
    }
}
