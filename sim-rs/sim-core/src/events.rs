use serde::Serialize;
use tokio::sync::mpsc;
use tracing::warn;

use crate::{
    clock::{Clock, Timestamp},
    config::NodeId,
    model::{
        Block, EndorserBlock, EndorserBlockId, InputBlock, InputBlockHeader, InputBlockId,
        NoVoteReason, Transaction, TransactionId, VoteBundle,
    },
};

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
pub enum Event {
    Slot {
        number: u64,
    },
    TransactionGenerated {
        id: TransactionId,
        publisher: NodeId,
        bytes: u64,
    },
    TransactionSent {
        id: TransactionId,
        sender: NodeId,
        recipient: NodeId,
    },
    TransactionReceived {
        id: TransactionId,
        sender: NodeId,
        recipient: NodeId,
    },
    PraosBlockGenerated {
        slot: u64,
        producer: NodeId,
        vrf: u64,
        transactions: Vec<TransactionId>,
    },
    PraosBlockSent {
        slot: u64,
        sender: NodeId,
        recipient: NodeId,
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
    InputBlockSent {
        #[serde(flatten)]
        id: InputBlockId,
        sender: NodeId,
        recipient: NodeId,
    },
    InputBlockReceived {
        #[serde(flatten)]
        id: InputBlockId,
        sender: NodeId,
        recipient: NodeId,
    },
    EndorserBlockGenerated {
        #[serde(flatten)]
        id: EndorserBlockId,
        input_blocks: Vec<InputBlockId>,
    },
    EndorserBlockSent {
        #[serde(flatten)]
        id: EndorserBlockId,
        sender: NodeId,
        recipient: NodeId,
    },
    EndorserBlockReceived {
        #[serde(flatten)]
        id: EndorserBlockId,
        sender: NodeId,
        recipient: NodeId,
    },
    VotesGenerated {
        slot: u64,
        producer: NodeId,
        ebs: Vec<EndorserBlockId>,
    },
    NoVote {
        slot: u64,
        producer: NodeId,
        eb: EndorserBlockId,
        reason: NoVoteReason,
    },
    VotesSent {
        slot: u64,
        producer: NodeId,
        sender: NodeId,
        recipient: NodeId,
    },
    VotesReceived {
        slot: u64,
        producer: NodeId,
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
            vrf: block.vrf,
            transactions: block.transactions.iter().map(|tx| tx.id).collect(),
        });
    }

    pub fn track_praos_block_sent(&self, block: &Block, sender: NodeId, recipient: NodeId) {
        self.send(Event::PraosBlockSent {
            slot: block.slot,
            sender,
            recipient,
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

    pub fn track_transaction_sent(&self, id: TransactionId, sender: NodeId, recipient: NodeId) {
        self.send(Event::TransactionSent {
            id,
            sender,
            recipient,
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

    pub fn track_ib_sent(&self, id: InputBlockId, sender: NodeId, recipient: NodeId) {
        self.send(Event::InputBlockSent {
            id,
            sender,
            recipient,
        });
    }

    pub fn track_ib_received(&self, id: InputBlockId, sender: NodeId, recipient: NodeId) {
        self.send(Event::InputBlockReceived {
            id,
            sender,
            recipient,
        });
    }

    pub fn track_eb_generated(&self, block: &EndorserBlock) {
        self.send(Event::EndorserBlockGenerated {
            id: block.id(),
            input_blocks: block.ibs.clone(),
        });
    }

    pub fn track_eb_sent(&self, id: EndorserBlockId, sender: NodeId, recipient: NodeId) {
        self.send(Event::EndorserBlockSent {
            id,
            sender,
            recipient,
        });
    }

    pub fn track_eb_received(&self, id: EndorserBlockId, sender: NodeId, recipient: NodeId) {
        self.send(Event::EndorserBlockReceived {
            id,
            sender,
            recipient,
        });
    }

    pub fn track_votes_generated(&self, votes: &VoteBundle) {
        self.send(Event::VotesGenerated {
            slot: votes.slot,
            producer: votes.producer,
            ebs: votes.ebs.clone(),
        });
    }

    pub fn track_no_vote(
        &self,
        slot: u64,
        producer: NodeId,
        eb: EndorserBlockId,
        reason: NoVoteReason,
    ) {
        self.send(Event::NoVote {
            slot,
            producer,
            eb,
            reason,
        });
    }

    pub fn track_votes_sent(&self, votes: &VoteBundle, sender: NodeId, recipient: NodeId) {
        self.send(Event::VotesSent {
            slot: votes.slot,
            producer: votes.producer,
            sender,
            recipient,
        });
    }

    pub fn track_votes_received(&self, votes: &VoteBundle, sender: NodeId, recipient: NodeId) {
        self.send(Event::VotesReceived {
            slot: votes.slot,
            producer: votes.producer,
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
