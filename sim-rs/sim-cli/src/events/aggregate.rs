use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;
use sim_core::{
    clock::Timestamp,
    events::{Event, Node},
    model::{BlockId, TransactionId},
};

use super::{EndorserBlockId, InputBlockId, OutputEvent, VoteBundleId};

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum TransactionStatus {
    Created,
    InIb,
    InEb,
    OnChain,
}

#[derive(Serialize, Default)]
#[serde(rename_all = "camelCase")]
struct TransactionCounts {
    timestamp: Timestamp,
    created: u64,
    in_ib: u64,
    in_eb: u64,
    on_chain: u64,
}

#[derive(Default)]
pub struct TraceAggregator {
    current_time: Timestamp,
    nodes_updated: BTreeSet<Node>,
    transactions: BTreeMap<TransactionId, Transaction>,
    ibs: BTreeMap<InputBlockId, InputBlock>,
    ebs: BTreeMap<EndorserBlockId, EndorsementBlock>,
    rbs: Vec<Block>,
    tx_counts: Vec<TransactionCounts>,
    nodes: BTreeMap<Node, NodeAggregatedData>,
    bytes: BTreeMap<MessageId, u64>,
    tx_statuses: BTreeMap<TransactionId, TransactionStatus>,
    leios_txs: BTreeSet<TransactionId>,
    praos_txs: BTreeSet<TransactionId>,
}

impl TraceAggregator {
    pub fn new() -> Self {
        let mut me = Self::default();
        me.tx_counts.push(TransactionCounts::default());
        me
    }

    pub fn process(&mut self, event: OutputEvent) -> Option<AggregatedData> {
        match event.message {
            Event::TXGenerated {
                id,
                publisher,
                size_bytes,
                ..
            } => {
                self.transactions.insert(
                    id,
                    Transaction {
                        id,
                        bytes: size_bytes,
                    },
                );
                self.tx_statuses.insert(id, TransactionStatus::Created);
                self.track_data_generated(MessageId::TX(id), publisher, size_bytes);
            }
            Event::TXSent { id, sender, .. } => {
                self.track_data_sent(MessageId::TX(id), sender);
            }
            Event::TXReceived { id, recipient, .. } => {
                self.track_data_received(MessageId::TX(id), recipient);
            }
            Event::IBGenerated {
                id,
                slot,
                pipeline,
                producer,
                header_bytes,
                size_bytes,
                transactions,
                ..
            } => {
                self.ibs.insert(
                    id.clone(),
                    InputBlock {
                        id: id.to_string(),
                        slot,
                        pipeline,
                        header_bytes,
                        txs: transactions
                            .iter()
                            .map(|id| self.transactions.get(id).unwrap().clone())
                            .collect(),
                    },
                );
                for tx in transactions {
                    let status = self
                        .tx_statuses
                        .entry(tx)
                        .or_insert(TransactionStatus::InIb);
                    if *status == TransactionStatus::Created {
                        *status = TransactionStatus::InIb;
                    }
                }
                self.track_data_generated(MessageId::IB(id), producer, size_bytes);
            }
            Event::IBSent { id, sender, .. } => {
                self.track_data_sent(MessageId::IB(id), sender);
            }
            Event::IBReceived { id, recipient, .. } => {
                self.track_data_received(MessageId::IB(id), recipient);
            }
            Event::EBGenerated {
                id,
                slot,
                pipeline,
                producer,
                size_bytes,
                transactions,
                input_blocks,
                endorser_blocks,
                ..
            } => {
                self.ebs.insert(
                    id.clone(),
                    EndorsementBlock {
                        id: id.to_string(),
                        slot,
                        pipeline,
                        bytes: size_bytes,
                        txs: transactions.iter().map(|tx| tx.id).collect(),
                        ibs: input_blocks
                            .iter()
                            .map(|ib| self.ibs.get(&ib.id).unwrap().clone())
                            .collect(),
                        ebs: endorser_blocks
                            .iter()
                            .map(|eb| self.ebs.get(&eb.id).unwrap().clone())
                            .collect(),
                    },
                );
                for tx_id in input_blocks
                    .iter()
                    .map(|ib| self.ibs.get(&ib.id).unwrap())
                    .flat_map(|ib| ib.txs.iter())
                    .map(|tx| tx.id)
                    .chain(transactions.iter().map(|tx| tx.id))
                {
                    let status = self
                        .tx_statuses
                        .entry(tx_id)
                        .or_insert(TransactionStatus::InEb);
                    if matches!(status, TransactionStatus::Created | TransactionStatus::InIb) {
                        *status = TransactionStatus::InEb;
                    }
                }
                self.track_data_generated(MessageId::EB(id), producer, size_bytes);
            }
            Event::EBSent { id, sender, .. } => {
                self.track_data_sent(MessageId::EB(id), sender);
            }
            Event::EBReceived { id, recipient, .. } => {
                self.track_data_received(MessageId::EB(id), recipient);
            }
            Event::VTBundleGenerated {
                id,
                producer,
                size_bytes,
                ..
            } => {
                self.track_data_generated(MessageId::Votes(id), producer, size_bytes);
            }
            Event::VTBundleSent { id, sender, .. } => {
                self.track_data_sent(MessageId::Votes(id), sender);
            }
            Event::VTBundleReceived { id, recipient, .. } => {
                self.track_data_received(MessageId::Votes(id), recipient);
            }
            Event::RBGenerated {
                id,
                producer,
                size_bytes,
                transactions,
                header_bytes,
                endorsement,
                ..
            } => {
                for id in &transactions {
                    self.tx_statuses.insert(*id, TransactionStatus::OnChain);
                    self.praos_txs.insert(*id);
                }
                for tx in endorsement
                    .as_ref()
                    .and_then(|c| self.ebs.get(&c.eb.id))
                    .iter()
                    .flat_map(|eb| &eb.ibs)
                    .flat_map(|ib| ib.txs.iter())
                {
                    self.tx_statuses.insert(tx.id, TransactionStatus::OnChain);
                    self.leios_txs.insert(tx.id);
                }
                self.rbs.push(Block {
                    slot: id.slot,
                    txs: transactions
                        .iter()
                        .map(|id| self.transactions.get(id).unwrap().clone())
                        .collect(),
                    header_bytes,
                    cert: endorsement.map(|c| {
                        let eb = self.ebs.get(&c.eb.id).unwrap().clone();
                        Certificate {
                            bytes: c.size_bytes,
                            eb,
                        }
                    }),
                });
                self.track_data_generated(MessageId::PB(id), producer, size_bytes);
            }
            Event::RBSent { id, sender, .. } => {
                self.track_data_sent(MessageId::PB(id), sender);
            }
            Event::RBReceived { id, recipient, .. } => {
                self.track_data_received(MessageId::PB(id), recipient);
            }
            _ => {}
        };
        let current_chunk = (self.current_time - Timestamp::zero()).as_millis() / 250;
        let new_chunk = (event.time_s - Timestamp::zero()).as_millis() / 250;
        self.current_time = event.time_s;
        if current_chunk != new_chunk {
            if new_chunk.is_multiple_of(4) {
                let timestamp = Timestamp::from_secs((new_chunk / 4) as u64);
                self.tx_counts.push(self.produce_tx_counts(timestamp));
            }
            Some(self.produce_message())
        } else {
            None
        }
    }

    pub fn finish(mut self) -> Option<AggregatedData> {
        if self.nodes_updated.is_empty() {
            None
        } else {
            Some(self.produce_message())
        }
    }

    fn produce_tx_counts(&self, timestamp: Timestamp) -> TransactionCounts {
        let mut tx_counts = TransactionCounts {
            timestamp,
            ..TransactionCounts::default()
        };
        for status in self.tx_statuses.values() {
            match status {
                TransactionStatus::Created => tx_counts.created += 1,
                TransactionStatus::InIb => tx_counts.in_ib += 1,
                TransactionStatus::InEb => tx_counts.in_eb += 1,
                TransactionStatus::OnChain => tx_counts.on_chain += 1,
            }
        }
        tx_counts
    }

    fn produce_message(&mut self) -> AggregatedData {
        let nodes_updated = std::mem::take(&mut self.nodes_updated);
        AggregatedData {
            progress: self.current_time,
            nodes: self.nodes.clone(),
            global: GlobalAggregatedData {
                praos_tx_on_chain: self.praos_txs.len() as u64,
                leios_tx_on_chain: self.leios_txs.len() as u64,
            },
            blocks: std::mem::take(&mut self.rbs),
            transactions: std::mem::take(&mut self.tx_counts),
            last_nodes_updated: nodes_updated.into_iter().collect(),
        }
    }

    fn track_data_generated(&mut self, id: MessageId, producer: Node, bytes: u64) {
        self.nodes_updated.insert(producer.clone());
        let node_data = self.nodes.entry(producer).or_default();
        *node_data.generated.entry(id.kind()).or_default() += 1;
        self.bytes.insert(id, bytes);
    }

    fn track_data_sent(&mut self, id: MessageId, sender: Node) {
        self.nodes_updated.insert(sender.clone());
        let node_data = self.nodes.entry(sender).or_default();
        let bytes = self.bytes.get(&id).copied().unwrap_or_default();
        let stats = node_data.sent.entry(id.kind()).or_default();
        stats.count += 1;
        stats.bytes += bytes;
        node_data.bytes_sent += bytes;
    }

    fn track_data_received(&mut self, id: MessageId, recipient: Node) {
        self.nodes_updated.insert(recipient.clone());
        let node_data = self.nodes.entry(recipient).or_default();
        let bytes = self.bytes.get(&id).copied().unwrap_or_default();
        let stats = node_data.received.entry(id.kind()).or_default();
        stats.count += 1;
        stats.bytes += bytes;
        node_data.bytes_received += bytes;
    }
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AggregatedData {
    progress: Timestamp,
    nodes: BTreeMap<Node, NodeAggregatedData>,
    global: GlobalAggregatedData,
    blocks: Vec<Block>,
    transactions: Vec<TransactionCounts>,
    last_nodes_updated: Vec<Node>,
}

#[derive(Serialize, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
#[serde(rename_all = "lowercase")]
enum MessageKind {
    TX,
    IB,
    EB,
    Votes,
    PB,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum MessageId {
    TX(TransactionId),
    IB(InputBlockId),
    EB(EndorserBlockId),
    Votes(VoteBundleId),
    PB(BlockId<Node>),
}

impl MessageId {
    fn kind(&self) -> MessageKind {
        match self {
            Self::TX(_) => MessageKind::TX,
            Self::IB(_) => MessageKind::IB,
            Self::EB(_) => MessageKind::EB,
            Self::Votes(_) => MessageKind::Votes,
            Self::PB(_) => MessageKind::PB,
        }
    }
}

#[derive(Serialize, Default, Clone)]
#[serde(rename_all = "camelCase")]
struct MessageStats {
    count: u64,
    bytes: u64,
}

#[derive(Serialize, Default, Clone)]
#[serde(rename_all = "camelCase")]
struct NodeAggregatedData {
    bytes_sent: u64,
    bytes_received: u64,
    generated: BTreeMap<MessageKind, u64>,
    sent: BTreeMap<MessageKind, MessageStats>,
    received: BTreeMap<MessageKind, MessageStats>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct GlobalAggregatedData {
    praos_tx_on_chain: u64,
    leios_tx_on_chain: u64,
}

#[derive(Serialize, Clone)]
#[serde(rename_all = "camelCase")]
struct Block {
    slot: u64,
    txs: Vec<Transaction>,
    header_bytes: u64,
    cert: Option<Certificate>,
}

#[derive(Serialize, Clone)]
#[serde(rename_all = "camelCase")]
struct Transaction {
    id: TransactionId,
    bytes: u64,
}

#[derive(Serialize, Clone)]
#[serde(rename_all = "camelCase")]
struct Certificate {
    bytes: u64,
    eb: EndorsementBlock,
}

#[derive(Serialize, Clone)]
#[serde(rename_all = "camelCase")]
struct EndorsementBlock {
    id: String,
    slot: u64,
    pipeline: u64,
    bytes: u64,
    txs: Vec<TransactionId>,
    ibs: Vec<InputBlock>,
    ebs: Vec<EndorsementBlock>,
}

#[derive(Serialize, Clone)]
#[serde(rename_all = "camelCase")]
struct InputBlock {
    id: String,
    slot: u64,
    pipeline: u64,
    header_bytes: u64,
    txs: Vec<Transaction>,
}
