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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearRankingBlockHeader {
    pub id: BlockId,
    pub vrf: u64,
    pub parent: Option<BlockId>,
    pub bytes: u64,
    pub eb_announcement: Option<EndorserBlockId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearRankingBlock {
    pub header: LinearRankingBlockHeader,
    pub transactions: Vec<Arc<Transaction>>,
    pub endorsement: Option<Endorsement>,
}

impl LinearRankingBlock {
    pub fn bytes(&self) -> u64 {
        self.header.bytes + self.transactions.iter().map(|t| t.bytes).sum::<u64>()
    }
}

id_wrapper!(TransactionId, u64);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transaction {
    pub id: TransactionId,
    pub shard: u64,
    pub bytes: u64,
    pub input_id: u64,
    pub overcollateralization_factor: u64,
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
    pub shard: u64,
    pub bytes: u64,
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

#[derive(Debug)]
pub struct StracciatellaEndorserBlock {
    pub slot: u64,
    pub pipeline: u64,
    pub producer: NodeId,
    pub shard: u64,
    pub bytes: u64,
    pub txs: Vec<Arc<Transaction>>,
    pub ebs: Vec<EndorserBlockId>,
}
impl StracciatellaEndorserBlock {
    pub fn id(&self) -> EndorserBlockId {
        EndorserBlockId {
            slot: self.slot,
            pipeline: self.pipeline,
            producer: self.producer,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearEndorserBlock {
    pub slot: u64,
    pub producer: NodeId,
    pub bytes: u64,
    pub txs: Vec<Arc<Transaction>>,
}
impl LinearEndorserBlock {
    pub fn id(&self) -> EndorserBlockId {
        EndorserBlockId {
            slot: self.slot,
            pipeline: 0,
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

/// CIP-0164 vote class.  Persistent voters carry a 2-byte
/// persistent-voter id; non-persistent carry the 28-byte pool id
/// plus a 48-byte eligibility signature.  Both classes finish with
/// the 48-byte BLS vote signature.  See CDDL diff in
/// `docs/cddl/diffs/common/votes-certificates.md`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum VoteKind {
    Persistent,
    NonPersistent,
}

/// Wire identity for a single CIP-0164 vote — one voter, one EB,
/// one kind.  CIP partitions PV and NPV pools disjointly so the
/// pair `(voter, eb)` is unambiguous in practice; the kind tags the
/// id for indexing / dedup convenience.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VoteId<Node = NodeId> {
    pub slot: u64,
    pub voter: Node,
    pub eb: EndorserBlockId<Node>,
    pub kind: VoteKind,
}
impl<Node: Display> Display for VoteId<Node> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let kind = match self.kind {
            VoteKind::Persistent => "PV",
            VoteKind::NonPersistent => "NPV",
        };
        f.write_fmt(format_args!(
            "{}-{}-{}-{}",
            self.slot, self.voter, self.eb, kind
        ))
    }
}
impl<Node: Display> Serialize for VoteId<Node> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

/// A single CIP-0164 vote on the sim wire.  Carries the
/// eligibility-derivation inputs the verifier needs (PV: implicit
/// from `id.voter`; NPV: explicit 48-byte signature) but no weight —
/// weight is recomputed at verification time from the local
/// persistent-committee + stake registry, matching
/// `shared_consensus::elections::Elections::weight_for`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Vote {
    pub id: VoteId,
    pub bytes: u64,
    /// `Some(sig)` for NPV (carries the BLS eligibility signature);
    /// `None` for PV (voter is identified by `id.voter` and verified
    /// against the persistent-committee registry).
    pub eligibility_signature: Option<Vec<u8>>,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NoVoteReason {
    InvalidSlot,
    ExtraIB,
    MissingIB,
    MissingEB,
    LateIBHeader,
    EquivocatedIB,
    ExtraTX,
    MissingTX,
    UncertifiedEBReference,
    LateRBHeader,
    LateEB,
    WrongEB,
    /// CIP-0164 RB-header equivocation detected at the EB's slot —
    /// honest voters abstain from voting for any EB associated with
    /// the equivocating slot.
    EquivocatingRB,
}

#[derive(Debug, Clone, Serialize)]
pub enum TransactionLostReason {
    IBExpired,
    EBExpired,
    GeneratedBacklogFull,
    PeerBacklogFull,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct Endorsement<Node: Display = NodeId> {
    pub eb: EndorserBlockId<Node>,
    pub size_bytes: u64,
    pub votes: BTreeMap<Node, usize>,
}
