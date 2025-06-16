use std::{collections::BTreeMap, fmt::Display, sync::Arc};

use crate::{clock::Timestamp, config::NodeId};
use serde::Serialize;

macro_rules! id_wrapper {
    ($outer:ident, $inner:ty) => {
        #[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
        pub struct $outer($inner);
        impl Display for $outer {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.fmt(f)
            }
        }
        impl Serialize for $outer {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                serializer.serialize_str(&self.0.to_string())
            }
        }
        impl $outer {
            #[allow(unused)]
            pub fn new(value: $inner) -> Self {
                Self(value)
            }
        }
    };
}

#[derive(Clone, Debug, Serialize)]
pub struct CpuTaskId<Node = NodeId> {
    pub node: Node,
    pub index: u64,
}

impl<Node: Display> Display for CpuTaskId<Node> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}-{}", self.node, self.index))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BlockId<Node = NodeId> {
    pub slot: u64,
    pub producer: Node,
}

impl<Node: Display> Display for BlockId<Node> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}-{}", self.slot, self.producer))
    }
}

impl<Node: Display> Serialize for BlockId<Node> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

#[derive(Clone, Debug)]
pub struct Block {
    pub id: BlockId,
    pub vrf: u64,
    pub parent: Option<BlockId>,
    pub header_bytes: u64,
    pub endorsement: Option<Endorsement>,
    pub transactions: Vec<Arc<Transaction>>,
}

impl Block {
    pub fn bytes(&self) -> u64 {
        self.header_bytes
            + self
                .endorsement
                .as_ref()
                .map(|e| e.size_bytes)
                .unwrap_or_default()
            + self.transactions.iter().map(|t| t.bytes).sum::<u64>()
    }
}

id_wrapper!(TransactionId, u64);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transaction {
    pub id: TransactionId,
    pub shard: u64,
    pub bytes: u64,
    pub input_id: u64,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InputBlockId<Node = NodeId> {
    pub slot: u64,
    pub pipeline: u64,
    pub producer: Node,
    /// Need this field to distinguish IBs from the same slot+producer.
    /// The real implementation can use the VRF proof for that.
    pub index: u64,
}

impl<Node: Display> Display for InputBlockId<Node> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{}-{}-{}",
            self.slot, self.producer, self.index
        ))
    }
}

impl<Node: Display> Serialize for InputBlockId<Node> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct InputBlockHeader {
    pub id: InputBlockId,
    pub vrf: u64,
    pub shard: u64,
    pub timestamp: Timestamp,
    pub bytes: u64,
}

#[derive(Debug)]
pub struct InputBlock {
    pub header: InputBlockHeader,
    pub tx_payload_bytes: u64,
    pub transactions: Vec<Arc<Transaction>>,
    pub rb_ref: Option<BlockId>,
}
impl InputBlock {
    pub fn bytes(&self) -> u64 {
        self.header.bytes + self.tx_payload_bytes
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EndorserBlockId<Node = NodeId> {
    pub slot: u64,
    pub pipeline: u64,
    pub producer: Node,
}
impl<Node: Display> Display for EndorserBlockId<Node> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}-{}", self.slot, self.producer))
    }
}
impl<Node: Display> Serialize for EndorserBlockId<Node> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

#[derive(Debug)]
pub struct EndorserBlock {
    pub slot: u64,
    pub pipeline: u64,
    pub producer: NodeId,
    pub bytes: u64,
    pub txs: Vec<TransactionId>,
    pub ibs: Vec<InputBlockId>,
    pub ebs: Vec<EndorserBlockId>,
}
impl EndorserBlock {
    pub fn id(&self) -> EndorserBlockId {
        EndorserBlockId {
            slot: self.slot,
            pipeline: self.pipeline,
            producer: self.producer,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VoteBundleId<Node = NodeId> {
    pub slot: u64,
    pub pipeline: u64,
    pub producer: Node,
}
impl<Node: Display> Display for VoteBundleId<Node> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}-{}", self.slot, self.producer))
    }
}
impl<Node: Display> Serialize for VoteBundleId<Node> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VoteBundle {
    pub id: VoteBundleId,
    pub bytes: u64,
    pub ebs: BTreeMap<EndorserBlockId, usize>,
}

#[derive(Debug, Clone, Serialize)]
pub enum NoVoteReason {
    InvalidSlot,
    ExtraIB,
    MissingIB,
    MissingEB,
    ExtraTX,
    MissingTX,
    UncertifiedEBReference,
}

#[derive(Debug, Clone, Serialize)]
pub enum TransactionLostReason {
    IBExpired,
    EBExpired,
}

#[derive(Clone, Debug, Serialize)]
pub struct Endorsement<Node: Display = NodeId> {
    pub eb: EndorserBlockId<Node>,
    pub size_bytes: u64,
    pub votes: BTreeMap<Node, usize>,
}
