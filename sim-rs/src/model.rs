use std::{
    fmt::Display,
    hash::{DefaultHasher, Hash, Hasher},
    sync::Arc,
};

use crate::{clock::Timestamp, config::NodeId};
use serde::Serialize;

macro_rules! id_wrapper {
    ($outer:ident, $inner:ty) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize)]
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

#[derive(Clone, PartialEq, Eq)]
pub struct Block {
    pub slot: u64,
    pub producer: NodeId,
    pub conflicts: Vec<NodeId>,
    pub transactions: Vec<Arc<Transaction>>,
}

id_wrapper!(TransactionId, u64);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transaction {
    pub id: TransactionId,
    pub bytes: u64,
}

id_wrapper!(InputBlockId, u64);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct InputBlockHeader {
    pub slot: u64,
    pub producer: NodeId,
    /// Need this field to distinguish IBs from the same slot+producer.
    /// The real implementation can use the VRF proof for that.
    pub index: u64,
    pub timestamp: Timestamp,
}
impl InputBlockHeader {
    pub fn id(&self) -> InputBlockId {
        let mut hasher = DefaultHasher::new();
        (self.slot, self.producer, self.index).hash(&mut hasher);
        InputBlockId(hasher.finish())
    }
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