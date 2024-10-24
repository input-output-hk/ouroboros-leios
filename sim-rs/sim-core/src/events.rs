use std::sync::Arc;

use tokio::sync::mpsc;
use tracing::warn;

use crate::{
    clock::{Clock, Timestamp},
    config::NodeId,
    model::{Block, InputBlock, Transaction, TransactionId},
};

pub enum Event {
    Transaction {
        id: TransactionId,
        bytes: u64,
    },
    Slot {
        number: u64,
        block: Option<Block>,
    },
    BlockReceived {
        slot: u64,
        sender: NodeId,
        recipient: NodeId,
    },
    InputBlockGenerated {
        block: Arc<InputBlock>,
    },
    InputBlockReceived {
        block: Arc<InputBlock>,
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

    pub fn track_slot(&self, number: u64, block: Option<Block>) {
        self.send(Event::Slot { number, block });
    }

    pub fn track_block_received(&self, slot: u64, sender: NodeId, recipient: NodeId) {
        self.send(Event::BlockReceived {
            slot,
            sender,
            recipient,
        });
    }

    pub fn track_transaction(&self, transaction: &Transaction) {
        self.send(Event::Transaction {
            id: transaction.id,
            bytes: transaction.bytes,
        });
    }

    pub fn track_ib_generated(&self, block: Arc<InputBlock>) {
        self.send(Event::InputBlockGenerated { block });
    }

    pub fn track_ib_received(&self, block: Arc<InputBlock>, sender: NodeId, recipient: NodeId) {
        self.send(Event::InputBlockReceived {
            block,
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
