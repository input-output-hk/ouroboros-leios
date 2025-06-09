use std::{collections::BTreeMap, fmt::Display, sync::Arc, time::Duration};

use serde::{Serialize, Serializer};
use tokio::sync::mpsc;
use tracing::warn;

use crate::{
    clock::{Clock, Timestamp},
    config::{NodeConfiguration, NodeId},
    model::{
        Block, BlockId, CpuTaskId, EndorserBlockId, InputBlockId, NoVoteReason, Transaction,
        TransactionId, TransactionLostReason, VoteBundle, VoteBundleId,
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

#[derive(Clone, Debug, Serialize)]
pub struct BlockRef<Id> {
    pub id: Id,
}

#[derive(Debug, Clone, Serialize)]
pub struct Endorsement<Node: Display = NodeId> {
    pub eb: BlockRef<EndorserBlockId<Node>>,
    pub size_bytes: u64,
    pub votes: BTreeMap<Node, usize>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
pub enum Event {
    GlobalSlot {
        slot: u64,
    },
    Slot {
        node: Node,
        slot: u64,
    },
    CpuTaskScheduled {
        task: CpuTaskId<Node>,
        task_type: String,
        subtasks: usize,
    },
    CpuTaskFinished {
        task: CpuTaskId<Node>,
        task_type: String,
        #[serde(serialize_with = "duration_as_secs")]
        cpu_time_s: Duration,
        #[serde(serialize_with = "duration_as_secs")]
        wall_time_s: Duration,
        extra: String,
    },
    Cpu {
        task: CpuTaskId<Node>,
        node: String,
        #[serde(serialize_with = "duration_as_secs")]
        cpu_time_s: Duration,
        task_label: String,
        task_type: String,
        id: String,
    },
    TXGenerated {
        id: TransactionId,
        publisher: Node,
        size_bytes: u64,
        shard: u64,
    },
    TXSent {
        id: TransactionId,
        sender: Node,
        recipient: Node,
        msg_size_bytes: u64,
    },
    TXReceived {
        id: TransactionId,
        sender: Node,
        recipient: Node,
    },
    TXLost {
        id: TransactionId,
        reason: TransactionLostReason,
    },
    RBLotteryWon {
        id: BlockId<Node>,
        slot: u64,
        producer: Node,
    },
    RBGenerated {
        id: BlockId<Node>,
        slot: u64,
        producer: Node,
        vrf: u64,
        parent: Option<BlockRef<BlockId<Node>>>,
        header_bytes: u64,
        size_bytes: u64,
        endorsement: Option<Endorsement<Node>>,
        transactions: Vec<TransactionId>,
    },
    RBSent {
        id: BlockId<Node>,
        slot: u64,
        producer: Node,
        sender: Node,
        recipient: Node,
        msg_size_bytes: u64,
    },
    RBReceived {
        id: BlockId<Node>,
        slot: u64,
        producer: Node,
        sender: Node,
        recipient: Node,
    },
    IBLotteryWon {
        id: InputBlockId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
        index: u64,
    },
    IBGenerated {
        id: InputBlockId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
        index: u64,
        shard: u64,
        header_bytes: u64,
        tx_payload_bytes: u64,
        size_bytes: u64,
        transactions: Vec<TransactionId>,
    },
    NoIBGenerated {
        node: Node,
        slot: u64,
    },
    IBSent {
        id: InputBlockId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
        index: u64,
        sender: Node,
        recipient: Node,
        msg_size_bytes: u64,
    },
    IBReceived {
        id: InputBlockId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
        index: u64,
        sender: Node,
        recipient: Node,
    },
    EBLotteryWon {
        id: EndorserBlockId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
    },
    EBGenerated {
        id: EndorserBlockId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
        size_bytes: u64,
        transactions: Vec<BlockRef<TransactionId>>,
        input_blocks: Vec<BlockRef<InputBlockId<Node>>>,
        endorser_blocks: Vec<BlockRef<EndorserBlockId<Node>>>,
    },
    NoEBGenerated {
        node: Node,
        slot: u64,
    },
    EBSent {
        id: EndorserBlockId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
        sender: Node,
        recipient: Node,
        msg_size_bytes: u64,
    },
    EBReceived {
        id: EndorserBlockId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
        sender: Node,
        recipient: Node,
    },
    VTLotteryWon {
        id: VoteBundleId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
    },
    VTBundleGenerated {
        id: VoteBundleId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
        size_bytes: u64,
        votes: Votes<Node>,
    },
    NoVTBundleGenerated {
        node: Node,
        slot: u64,
    },
    VTBundleNotGenerated {
        slot: u64,
        pipeline: u64,
        producer: Node,
        eb: EndorserBlockId<Node>,
        reason: NoVoteReason,
    },
    VTBundleSent {
        id: VoteBundleId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
        sender: Node,
        recipient: Node,
        msg_size_bytes: u64,
    },
    VTBundleReceived {
        id: VoteBundleId<Node>,
        slot: u64,
        pipeline: u64,
        producer: Node,
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
    node_names: Arc<BTreeMap<NodeId, Arc<String>>>,
}

impl EventTracker {
    pub fn new(
        sender: mpsc::UnboundedSender<(Event, Timestamp)>,
        clock: Clock,
        nodes: &[NodeConfiguration],
    ) -> Self {
        let node_names = Arc::new(
            nodes
                .iter()
                .map(|n| (n.id, Arc::new(n.name.clone())))
                .collect(),
        );
        Self {
            sender,
            clock,
            node_names,
        }
    }

    pub fn track_global_slot(&self, slot: u64) {
        self.send(Event::GlobalSlot { slot });
    }

    pub fn track_slot(&self, node: NodeId, slot: u64) {
        self.send(Event::Slot {
            node: self.to_node(node),
            slot,
        });
    }

    pub fn track_cpu_task_scheduled(&self, task_id: CpuTaskId, task_type: String, subtasks: usize) {
        self.send(Event::CpuTaskScheduled {
            task: self.to_task(task_id),
            task_type,
            subtasks,
        });
    }

    pub fn track_cpu_task_finished(
        &self,
        task_id: CpuTaskId,
        task_type: String,
        cpu_time: Duration,
        wall_time: Duration,
        extra: String,
    ) {
        self.send(Event::CpuTaskFinished {
            task: self.to_task(task_id),
            task_type,
            cpu_time_s: cpu_time,
            wall_time_s: wall_time,
            extra,
        });
    }

    pub fn track_cpu_subtask_started(
        &self,
        task_id: CpuTaskId,
        task_type: String,
        subtask_id: u64,
        duration: Duration,
    ) {
        let task = self.to_task(task_id);
        let id = format!("{}-{}", task, subtask_id);
        self.send(Event::Cpu {
            node: task.node.to_string(),
            task,
            task_label: format!("{task_type}: {id}"),
            id,
            task_type,
            cpu_time_s: duration,
        });
    }

    pub fn track_praos_block_lottery_won(&self, block: &Block) {
        self.send(Event::RBLotteryWon {
            id: self.to_block(block.id),
            slot: block.id.slot,
            producer: self.to_node(block.id.producer),
        });
    }

    pub fn track_praos_block_generated(&self, block: &Block) {
        self.send(Event::RBGenerated {
            id: self.to_block(block.id),
            slot: block.id.slot,
            producer: self.to_node(block.id.producer),
            vrf: block.vrf,
            parent: block.parent.map(|id| BlockRef {
                id: self.to_block(id),
            }),
            header_bytes: block.header_bytes,
            size_bytes: block.bytes(),
            endorsement: block.endorsement.as_ref().map(|e| Endorsement {
                eb: BlockRef {
                    id: self.to_endorser_block(e.eb),
                },
                size_bytes: e.size_bytes,
                votes: e
                    .votes
                    .iter()
                    .map(|(k, v)| (self.to_node(*k), *v))
                    .collect(),
            }),
            transactions: block.transactions.iter().map(|tx| tx.id).collect(),
        });
    }

    pub fn track_praos_block_sent(&self, block: &Block, sender: NodeId, recipient: NodeId) {
        self.send(Event::RBSent {
            id: self.to_block(block.id),
            slot: block.id.slot,
            producer: self.to_node(block.id.producer),
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
            msg_size_bytes: block.bytes(),
        });
    }

    pub fn track_praos_block_received(&self, block: &Block, sender: NodeId, recipient: NodeId) {
        self.send(Event::RBReceived {
            id: self.to_block(block.id),
            slot: block.id.slot,
            producer: self.to_node(block.id.producer),
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_transaction_generated(&self, transaction: &Transaction, publisher: NodeId) {
        self.send(Event::TXGenerated {
            id: transaction.id,
            publisher: self.to_node(publisher),
            size_bytes: transaction.bytes,
            shard: transaction.shard,
        });
    }

    pub fn track_transaction_sent(
        &self,
        transaction: &Transaction,
        sender: NodeId,
        recipient: NodeId,
    ) {
        self.send(Event::TXSent {
            id: transaction.id,
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
            msg_size_bytes: transaction.bytes,
        });
    }

    pub fn track_transaction_received(&self, id: TransactionId, sender: NodeId, recipient: NodeId) {
        self.send(Event::TXReceived {
            id,
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_ib_lottery_won(&self, id: InputBlockId) {
        self.send(Event::IBLotteryWon {
            id: self.to_input_block(id),
            slot: id.slot,
            pipeline: id.pipeline,
            producer: self.to_node(id.producer),
            index: id.index,
        });
    }

    pub fn track_ib_generated(&self, block: &crate::model::InputBlock) {
        let header_bytes = block.header.bytes;
        let tx_payload_bytes = block.tx_payload_bytes;
        self.send(Event::IBGenerated {
            id: self.to_input_block(block.header.id),
            slot: block.header.id.slot,
            pipeline: block.header.id.pipeline,
            producer: self.to_node(block.header.id.producer),
            index: block.header.id.index,
            shard: block.header.shard,
            header_bytes,
            tx_payload_bytes,
            size_bytes: header_bytes + tx_payload_bytes,
            transactions: block.transactions.iter().map(|tx| tx.id).collect(),
        });
    }

    pub fn track_no_ib_generated(&self, node: NodeId, slot: u64) {
        self.send(Event::NoIBGenerated {
            node: self.to_node(node),
            slot,
        });
    }

    pub fn track_ib_sent(
        &self,
        block: &crate::model::InputBlock,
        sender: NodeId,
        recipient: NodeId,
    ) {
        let id = block.header.id;
        self.send(Event::IBSent {
            id: self.to_input_block(id),
            slot: id.slot,
            pipeline: id.pipeline,
            producer: self.to_node(id.producer),
            index: id.index,
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
            msg_size_bytes: block.bytes(),
        });
    }

    pub fn track_ib_received(&self, id: InputBlockId, sender: NodeId, recipient: NodeId) {
        self.send(Event::IBReceived {
            id: self.to_input_block(id),
            slot: id.slot,
            pipeline: id.pipeline,
            producer: self.to_node(id.producer),
            index: id.index,
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_eb_lottery_won(&self, id: EndorserBlockId) {
        self.send(Event::EBLotteryWon {
            id: self.to_endorser_block(id),
            slot: id.slot,
            pipeline: id.pipeline,
            producer: self.to_node(id.producer),
        });
    }

    pub fn track_eb_generated(&self, block: &crate::model::EndorserBlock) {
        self.send(Event::EBGenerated {
            id: self.to_endorser_block(block.id()),
            slot: block.slot,
            pipeline: block.pipeline,
            producer: self.to_node(block.producer),
            size_bytes: block.bytes,
            transactions: block.txs.iter().map(|id| BlockRef { id: *id }).collect(),
            input_blocks: block
                .ibs
                .iter()
                .map(|id| BlockRef {
                    id: self.to_input_block(*id),
                })
                .collect(),
            endorser_blocks: block
                .ebs
                .iter()
                .map(|id| BlockRef {
                    id: self.to_endorser_block(*id),
                })
                .collect(),
        });
    }

    pub fn track_no_eb_generated(&self, node: NodeId, slot: u64) {
        self.send(Event::NoEBGenerated {
            node: self.to_node(node),
            slot,
        });
    }

    pub fn track_eb_sent(
        &self,
        block: &crate::model::EndorserBlock,
        sender: NodeId,
        recipient: NodeId,
    ) {
        self.send(Event::EBSent {
            id: self.to_endorser_block(block.id()),
            slot: block.slot,
            pipeline: block.pipeline,
            producer: self.to_node(block.producer),
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
            msg_size_bytes: block.bytes,
        });
    }

    pub fn track_eb_received(&self, id: EndorserBlockId, sender: NodeId, recipient: NodeId) {
        self.send(Event::EBReceived {
            id: self.to_endorser_block(id),
            slot: id.slot,
            pipeline: id.pipeline,
            producer: self.to_node(id.producer),
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
        });
    }

    pub fn track_vote_lottery_won(&self, id: VoteBundleId) {
        self.send(Event::VTLotteryWon {
            id: self.to_vote_bundle(id),
            slot: id.slot,
            pipeline: id.pipeline,
            producer: self.to_node(id.producer),
        });
    }

    pub fn track_votes_generated(&self, votes: &VoteBundle) {
        self.send(Event::VTBundleGenerated {
            id: self.to_vote_bundle(votes.id),
            slot: votes.id.slot,
            pipeline: votes.id.pipeline,
            producer: self.to_node(votes.id.producer),
            size_bytes: votes.bytes,
            votes: Votes(
                votes
                    .ebs
                    .iter()
                    .map(|(node, count)| (self.to_endorser_block(*node), *count))
                    .collect(),
            ),
        });
    }

    pub fn track_no_vote_generated(&self, node: NodeId, slot: u64) {
        self.send(Event::NoVTBundleGenerated {
            node: self.to_node(node),
            slot,
        });
    }

    pub fn track_no_vote(
        &self,
        slot: u64,
        pipeline: u64,
        producer: NodeId,
        eb: EndorserBlockId,
        reason: NoVoteReason,
    ) {
        self.send(Event::VTBundleNotGenerated {
            slot,
            pipeline,
            producer: self.to_node(producer),
            eb: self.to_endorser_block(eb),
            reason,
        });
    }

    pub fn track_votes_sent(&self, votes: &VoteBundle, sender: NodeId, recipient: NodeId) {
        self.send(Event::VTBundleSent {
            id: self.to_vote_bundle(votes.id),
            slot: votes.id.slot,
            pipeline: votes.id.pipeline,
            producer: self.to_node(votes.id.producer),
            sender: self.to_node(sender),
            recipient: self.to_node(recipient),
            msg_size_bytes: votes.bytes,
        });
    }

    pub fn track_votes_received(&self, votes: &VoteBundle, sender: NodeId, recipient: NodeId) {
        self.send(Event::VTBundleReceived {
            id: self.to_vote_bundle(votes.id),
            slot: votes.id.slot,
            pipeline: votes.id.pipeline,
            producer: self.to_node(votes.id.producer),
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

    fn to_block(&self, id: BlockId) -> BlockId<Node> {
        BlockId {
            slot: id.slot,
            producer: self.to_node(id.producer),
        }
    }

    fn to_input_block(&self, id: InputBlockId) -> InputBlockId<Node> {
        InputBlockId {
            slot: id.slot,
            pipeline: id.pipeline,
            producer: self.to_node(id.producer),
            index: id.index,
        }
    }

    fn to_endorser_block(&self, id: EndorserBlockId) -> EndorserBlockId<Node> {
        EndorserBlockId {
            slot: id.slot,
            pipeline: id.pipeline,
            producer: self.to_node(id.producer),
        }
    }

    fn to_vote_bundle(&self, id: VoteBundleId) -> VoteBundleId<Node> {
        VoteBundleId {
            slot: id.slot,
            pipeline: id.pipeline,
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

fn duration_as_secs<S: Serializer>(duration: &Duration, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_f32(duration.as_secs_f32())
}
