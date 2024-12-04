use std::{fmt::Display, sync::Arc};

use crate::{clock::Timestamp, config::NodeId};
use serde::{ser::SerializeStruct, Serialize};

macro_rules! id_wrapper {
    ($outer:ident, $inner:ty) => {
        #[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize)]
        pub struct $outer($inner);
        impl Display for $outer {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.fmt(f)
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub slot: u64,
    pub producer: NodeId,
    pub vrf: u64,
    pub transactions: Vec<Arc<Transaction>>,
}

id_wrapper!(TransactionId, u64);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transaction {
    pub id: TransactionId,
    pub shard: u64,
    pub bytes: u64,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InputBlockId {
    pub slot: u64,
    pub producer: NodeId,
    /// Need this field to distinguish IBs from the same slot+producer.
    /// The real implementation can use the VRF proof for that.
    pub index: u64,
}

impl Display for InputBlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{}-{}-{}",
            self.slot, self.producer, self.index
        ))
    }
}

impl Serialize for InputBlockId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut obj = serializer.serialize_struct("InputBlockId", 4)?;
        obj.serialize_field("id", &self.to_string())?;
        obj.serialize_field("slot", &self.slot)?;
        obj.serialize_field("producer", &self.producer)?;
        obj.serialize_field("index", &self.index)?;
        obj.end()
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Serialize)]
pub struct InputBlockHeader {
    #[serde(flatten)]
    pub id: InputBlockId,
    pub vrf: u64,
    pub timestamp: Timestamp,
}

#[derive(Debug)]
pub struct InputBlock {
    pub header: InputBlockHeader,
    pub transactions: Vec<Arc<Transaction>>,
}
impl InputBlock {
    pub fn bytes(&self) -> u64 {
        self.transactions.iter().map(|tx| tx.bytes).sum()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EndorserBlockId {
    pub slot: u64,
    pub producer: NodeId,
}
impl Display for EndorserBlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}-{}", self.slot, self.producer))
    }
}
impl Serialize for EndorserBlockId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut obj = serializer.serialize_struct("EndorserBlockId", 4)?;
        obj.serialize_field("id", &self.to_string())?;
        obj.serialize_field("slot", &self.slot)?;
        obj.serialize_field("producer", &self.producer)?;
        obj.end()
    }
}

#[derive(Debug)]
pub struct EndorserBlock {
    pub slot: u64,
    pub producer: NodeId,
    // The real impl will store hashes
    pub ibs: Vec<InputBlockId>,
}
impl EndorserBlock {
    pub fn id(&self) -> EndorserBlockId {
        EndorserBlockId {
            slot: self.slot,
            producer: self.producer,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VoteBundleId {
    pub slot: u64,
    pub producer: NodeId,
}
impl Display for VoteBundleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}-{}", self.slot, self.producer))
    }
}
impl Serialize for VoteBundleId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut obj = serializer.serialize_struct("VoteBundleId", 4)?;
        obj.serialize_field("id", &self.to_string())?;
        obj.serialize_field("slot", &self.slot)?;
        obj.serialize_field("producer", &self.producer)?;
        obj.end()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VoteBundle {
    pub id: VoteBundleId,
    pub ebs: Vec<EndorserBlockId>, // contains duplicates
}

#[derive(Debug, Clone, Serialize)]
pub enum NoVoteReason {
    InvalidSlot,
    ExtraIB,
    MissingIB,
}
