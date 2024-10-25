use serde::Serialize;
use tokio::sync::mpsc;
use tracing::warn;

use crate::{
    clock::{Clock, Timestamp},
    config::NodeId,
    model::{Block, InputBlock, InputBlockHeader, InputBlockId, Transaction, TransactionId},
};

#[derive(Debug, Clone, Serialize)]
pub enum Event {
    Slot {
        number: u64,
    },
    TransactionGenerated {
        id: TransactionId,
        publisher: NodeId,
        bytes: u64,
    },
    TransactionReceived {
        id: TransactionId,
        sender: NodeId,
        recipient: NodeId,
    },
    PraosBlockGenerated {
        slot: u64,
        producer: NodeId,
        transactions: Vec<TransactionId>,
        conflicts: Vec<NodeId>,
    },
    PraosBlockReceived {
        slot: u64,
        sender: NodeId,
        recipient: NodeId,
    },
    InputBlockGenerated {
        #[serde(flatten)]
        header: InputBlockHeader,
        transactions: Vec<TransactionId>,
    },
    InputBlockReceived {
        #[serde(flatten)]
        id: InputBlockId,
        sender: NodeId,
        recipient: NodeId,
    },
}

#[derive(Clone)]
pub struct EventTracker {
    sender: mpsc::UnboundedSender<(Event, Timestamp)>,
    clock: Clock,
}

impl EventTracker {
    pub fn new(sender: mpsc::UnboundedSender<(Event, Timestamp)>, clock: Clock) -> Self {
        Self { sender, clock }
    }

    pub fn track_slot(&self, number: u64) {
        self.send(Event::Slot { number });
    }

    pub fn track_praos_block_generated(&self, block: &Block) {
        self.send(Event::PraosBlockGenerated {
            slot: block.slot,
            producer: block.producer,
            transactions: block.transactions.iter().map(|tx| tx.id).collect(),
            conflicts: block.conflicts.clone(),
        });
    }

    pub fn track_praos_block_received(&self, block: &Block, sender: NodeId, recipient: NodeId) {
        self.send(Event::PraosBlockReceived {
            slot: block.slot,
            sender,
            recipient,
        });
    }

    pub fn track_transaction_generated(&self, transaction: &Transaction, publisher: NodeId) {
        self.send(Event::TransactionGenerated {
            id: transaction.id,
            publisher,
            bytes: transaction.bytes,
        });
    }

    pub fn track_transaction_received(&self, id: TransactionId, sender: NodeId, recipient: NodeId) {
        self.send(Event::TransactionReceived {
            id,
            sender,
            recipient,
        });
    }

    pub fn track_ib_generated(&self, block: &InputBlock) {
        self.send(Event::InputBlockGenerated {
            header: block.header.clone(),
            transactions: block.transactions.iter().map(|tx| tx.id).collect(),
        });
    }

    pub fn track_ib_received(&self, id: InputBlockId, sender: NodeId, recipient: NodeId) {
        self.send(Event::InputBlockReceived {
            id,
            sender,
            recipient,
        });
    }

    fn send(&self, event: Event) {
        if self.sender.send((event, self.clock.now())).is_err() {
            warn!("tried sending event after aggregator finished");
        }
    }
}
