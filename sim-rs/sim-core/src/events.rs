use std::{collections::BTreeMap, fmt::Display, sync::Arc, time::Duration};

use serde::{Serialize, Serializer};
use tokio::sync::mpsc;
use tracing::warn;

use crate::{
    clock::{Clock, Timestamp},
    config::{NodeConfiguration, NodeId},
    model::{
        Block, CpuTaskId, Endorsement, EndorserBlockId, InputBlockId, NoVoteReason, Transaction,
        TransactionId, VoteBundle, VoteBundleId,
    },
};

#[derive(Debug, Clone)]
pub struct Node {
    pub id: NodeId,
    pub name: Arc<String>,
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)
    }
}

impl Serialize for Node {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.name)
    }
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.id.eq(&other.id)
    }
}
impl Eq for Node {}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.id.cmp(&other.id))
    }
}

impl Ord for Node {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
pub enum Event {
    Slot {
        number: u64,
    },
    CpuTaskScheduled {
        task: CpuTaskId<Node>,
        task_type: String,
        subtasks: usize,
    },
    CpuTaskFinished {
        task: CpuTaskId<Node>,
        task_type: String,
        extra: String,
    },
    CpuSubtaskStarted {
        task: CpuTaskId<Node>,
        subtask_id: u64,
        #[serde(serialize_with = "duration_as_nanos")]
        duration: Duration,
    },
    TransactionGenerated {
        id: TransactionId,
        publisher: Node,
        bytes: u64,
    },
    TransactionSent {
        id: TransactionId,
        sender: Node,
        recipient: Node,
    },
    TransactionReceived {
        id: TransactionId,
        sender: Node,
        recipient: Node,
    },
    PraosBlockLotteryWon {
        slot: u64,
        producer: Node,
    },
    PraosBlockGenerated {
        slot: u64,
        producer: Node,
        vrf: u64,
        header_bytes: u64,
        endorsement: Option<Endorsement<Node>>,
        transactions: Vec<TransactionId>,
    },
    PraosBlockSent {
        slot: u64,
        sender: Node,
        recipient: Node,
    },
    PraosBlockReceived {
        slot: u64,
        sender: Node,
        recipient: Node,
    },
    InputBlockLotteryWon {
        #[serde(flatten)]
        id: InputBlockId<Node>,
    },
    InputBlockGenerated {
        #[serde(flatten)]
        id: InputBlockId<Node>,
        header_bytes: u64,
        transactions: Vec<TransactionId>,
    },
    InputBlockSent {
        #[serde(flatten)]
        id: InputBlockId<Node>,
        sender: Node,
        recipient: Node,
    },
    InputBlockReceived {
        #[serde(flatten)]
        id: InputBlockId<Node>,
        sender: Node,
        recipient: Node,
    },
    EndorserBlockLotteryWon {
        #[serde(flatten)]
        id: EndorserBlockId<Node>,
    },
    EndorserBlockGenerated {
        #[serde(flatten)]
        id: EndorserBlockId<Node>,
        bytes: u64,
        input_blocks: Vec<InputBlockId<Node>>,
    },
    EndorserBlockSent {
        #[serde(flatten)]
        id: EndorserBlockId<Node>,
        sender: Node,
        recipient: Node,
    },
    EndorserBlockReceived {
        #[serde(flatten)]
        id: EndorserBlockId<Node>,
        sender: Node,
        recipient: Node,
    },
    VoteLotteryWon {
        #[serde(flatten)]
        id: VoteBundleId<Node>,
    },
    VotesGenerated {
        #[serde(flatten)]
        id: VoteBundleId<Node>,
        votes: Votes<Node>,
    },
    NoVote {
        slot: u64,
        producer: Node,
        eb: EndorserBlockId<Node>,
        reason: NoVoteReason,
    },
    VotesSent {
        #[serde(flatten)]
        id: VoteBundleId<Node>,
        sender: Node,
        recipient: Node,
    },
    VotesReceived {
        #[serde(flatten)]
        id: VoteBundleId<Node>,
        sender: Node,
        recipient: Node,
    },
}

#[derive(Debug, Clone)]
pub struct Votes<Node>(pub BTreeMap<EndorserBlockId<Node>, usize>);

impl<Node: Display> Serialize for Votes<Node> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.collect_map(self.0.iter().map(|(k, v)| (k.to_string(), *v)))
    }
}

#[derive(Clone)]
pub struct EventTracker {
    sender: mpsc::UnboundedSender<(Event, Timestamp)>,
    clock: Clock,
    node_names: BTreeMap<NodeId, Arc<String>>,
}

impl EventTracker {
    pub fn new(
        sender: mpsc::UnboundedSender<(Event, Timestamp)>,
        clock: Clock,
        nodes: &[NodeConfiguration],
    ) -> Self {
        let node_names = nodes
            .iter()
            .map(|n| (n.id, Arc::new(n.name.clone())))
            .collect();
        Self {
            sender,
            clock,
            node_names,
        }
    }

    pub fn track_slot(&self, number: u64) {
        self.send(Event::Slot { number });
    }

    pub fn track_cpu_task_scheduled(&self, task_id: CpuTaskId, task_type: String, subtasks: usize) {
        self.send(Event::CpuTaskScheduled {
            task: self.to_task(task_id),
            task_type,
            subtasks,
        });
    }

    pub fn track_cpu_task_finished(&self, task_id: CpuTaskId, task_type: String, extra: String) {
        self.send(Event::CpuTaskFinished {
            task: self.to_task(task_id),
            task_type,
            extra,
        });
    }

    pub fn track_cpu_subtask_started(
        &self,
        task_id: CpuTaskId,
        subtask_id: u64,
        duration: Duration,
    ) {
        self.send(Event::CpuSubtaskStarted {
            task: self.to_task(task_id),
            subtask_id,
            duration,
        });
    }

    pub fn track_praos_block_lottery_won(&self, block: &Block) {
        self.send(Event::PraosBlockLotteryWon {
            slot: block.slot,
            producer: self.to_node(block.producer),
        });
    }

    pub fn track_praos_block_generated(&self, block: &Block) {
        self.send(Event::PraosBlockGenerated {
            slot: block.slot,
            producer: self.to_node(block.producer),
            vrf: block.vrf,
            header_bytes: block.header_bytes,
            endorsement: block.endorsement.as_ref().map(|e| Endorsement {
                eb: self.to_endorser_block(e.eb),
                bytes: e.bytes,
                votes: e.votes.iter().map(|n| self.to_node(*n)).collect(),
            }),
            transactions: block.transactions.iter().map(|tx| tx.id).collect(),
        });
    }

    pub fn track_praos_block_sent(&self, block: &Block, sender: NodeId, recipient: NodeId) {
        self.send(Event::PraosBlockSent {
            slot: block.slot,
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_praos_block_received(&self, block: &Block, sender: NodeId, recipient: NodeId) {
        self.send(Event::PraosBlockReceived {
            slot: block.slot,
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_transaction_generated(&self, transaction: &Transaction, publisher: NodeId) {
        self.send(Event::TransactionGenerated {
            id: transaction.id,
            publisher: self.to_node(publisher),
            bytes: transaction.bytes,
        });
    }

    pub fn track_transaction_sent(&self, id: TransactionId, sender: NodeId, recipient: NodeId) {
        self.send(Event::TransactionSent {
            id,
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_transaction_received(&self, id: TransactionId, sender: NodeId, recipient: NodeId) {
        self.send(Event::TransactionReceived {
            id,
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_ib_lottery_won(&self, id: InputBlockId) {
        self.send(Event::InputBlockLotteryWon {
            id: self.to_input_block(id),
        });
    }

    pub fn track_ib_generated(&self, block: &crate::model::InputBlock) {
        self.send(Event::InputBlockGenerated {
            id: self.to_input_block(block.header.id),
            header_bytes: block.header.bytes,
            transactions: block.transactions.iter().map(|tx| tx.id).collect(),
        });
    }

    pub fn track_ib_sent(&self, id: InputBlockId, sender: NodeId, recipient: NodeId) {
        self.send(Event::InputBlockSent {
            id: self.to_input_block(id),
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_ib_received(&self, id: InputBlockId, sender: NodeId, recipient: NodeId) {
        self.send(Event::InputBlockReceived {
            id: self.to_input_block(id),
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_eb_lottery_won(&self, id: EndorserBlockId) {
        self.send(Event::EndorserBlockLotteryWon {
            id: self.to_endorser_block(id),
        });
    }

    pub fn track_eb_generated(&self, block: &crate::model::EndorserBlock) {
        self.send(Event::EndorserBlockGenerated {
            id: self.to_endorser_block(block.id()),
            bytes: block.bytes,
            input_blocks: block
                .ibs
                .iter()
                .map(|id| self.to_input_block(*id))
                .collect(),
        });
    }

    pub fn track_eb_sent(&self, id: EndorserBlockId, sender: NodeId, recipient: NodeId) {
        self.send(Event::EndorserBlockSent {
            id: self.to_endorser_block(id),
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_eb_received(&self, id: EndorserBlockId, sender: NodeId, recipient: NodeId) {
        self.send(Event::EndorserBlockReceived {
            id: self.to_endorser_block(id),
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_vote_lottery_won(&self, id: VoteBundleId) {
        self.send(Event::VoteLotteryWon {
            id: self.to_vote_bundle(id),
        });
    }

    pub fn track_votes_generated(&self, votes: &VoteBundle) {
        self.send(Event::VotesGenerated {
            id: self.to_vote_bundle(votes.id),
            votes: Votes(
                votes
                    .ebs
                    .iter()
                    .map(|(node, count)| (self.to_endorser_block(*node), *count))
                    .collect(),
            ),
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
            producer: self.to_node(producer),
            eb: self.to_endorser_block(eb),
            reason,
        });
    }

    pub fn track_votes_sent(&self, votes: &VoteBundle, sender: NodeId, recipient: NodeId) {
        self.send(Event::VotesSent {
            id: self.to_vote_bundle(votes.id),
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_votes_received(&self, votes: &VoteBundle, sender: NodeId, recipient: NodeId) {
        self.send(Event::VotesReceived {
            id: self.to_vote_bundle(votes.id),
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    fn send(&self, event: Event) {
        if self.sender.send((event, self.clock.now())).is_err() {
            warn!("tried sending event after aggregator finished");
        }
    }

    fn to_task(&self, id: CpuTaskId) -> CpuTaskId<Node> {
        CpuTaskId {
            node: self.to_node(id.node),
            index: id.index,
        }
    }

    fn to_input_block(&self, id: InputBlockId) -> InputBlockId<Node> {
        InputBlockId {
            slot: id.slot,
            producer: self.to_node(id.producer),
            index: id.index,
        }
    }

    fn to_endorser_block(&self, id: EndorserBlockId) -> EndorserBlockId<Node> {
        EndorserBlockId {
            slot: id.slot,
            producer: self.to_node(id.producer),
        }
    }

    fn to_vote_bundle(&self, id: VoteBundleId) -> VoteBundleId<Node> {
        VoteBundleId {
            slot: id.slot,
            producer: self.to_node(id.producer),
        }
    }

    fn to_node(&self, id: NodeId) -> Node {
        Node {
            id,
            name: self.node_names.get(&id).unwrap().clone(),
        }
    }
}

fn duration_as_nanos<S: Serializer>(duration: &Duration, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_u128(duration.as_nanos())
}
