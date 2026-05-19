//! Wire-level types shared between every Linear Leios adapter
//! (`linear_leios.rs`, `con_rs.rs`).  Holds the inter-node [`Message`]
//! enum, the CPU work-unit [`CpuTask`] enum, and the [`TimedEvent`]
//! enum used by the scheduler.
//!
//! Both adapters implement variants of CIP-0164 Linear Leios — they
//! exchange the same family of messages (RB / EB / Tx / Vote) and run
//! through the same CPU pipeline, so the types belong here rather
//! than in any one adapter file.
//!
//! Per-traffic-class encoding choice differs by adapter:
//! - `linear_leios.rs` uses the `Votes`/`VoteBundle` triplet (a
//!   sim-only aggregation, predates CIP-0164's per-vote model).
//! - `con-rs.rs` uses the per-vote `Vote` triplet to mirror the
//!   real CIP wire (one BLS signature per message).
//!
//! Variants intended only for one adapter are made unreachable in the
//! other's `handle_message` / `handle_cpu_task` matches; the
//! union-typing keeps the engine's message routing single-typed.

use std::{collections::BTreeMap, sync::Arc, time::Duration};

use crate::{
    clock::Timestamp,
    config::{CpuTimeConfig, NodeId},
    model::{
        BlockId, EndorserBlockId, LinearEndorserBlock as EndorserBlock,
        LinearRankingBlock as RankingBlock, LinearRankingBlockHeader as RankingBlockHeader,
        Transaction, TransactionId, Vote, VoteBundle, VoteBundleId, VoteId,
    },
    sim::{MiniProtocol, SimCpuTask, SimMessage},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Message {
    // TX propagation
    AnnounceTx(TransactionId),
    RequestTx(TransactionId),
    Tx(Arc<Transaction>),

    // RB header propagation
    AnnounceRBHeader(BlockId),
    RequestRBHeader(BlockId),
    RBHeader(
        RankingBlockHeader,
        bool, /* has_body */
        bool, /* has_eb */
    ),

    // RB body propagation
    AnnounceRB(BlockId),
    RequestRB(BlockId),
    RB(Arc<RankingBlock>),

    // EB propagation
    AnnounceEB(EndorserBlockId),
    RequestEB(EndorserBlockId),
    EB(Arc<EndorserBlock>),

    // EB-tx fetch (CIP-0164 LeiosFetch BlockTxs).  `con_rs.rs` only —
    // the receiver doesn't trust the inline `eb.txs` payload and
    // fetches missing tx bodies via this triplet instead.  `linear_leios.rs`
    // leaves the receiver waiting for normal tx diffusion to fill its
    // mempool.
    //
    // Wire-format mapping: `AnnounceEBTxs` ↔ `MsgLeiosBlockTxsOffer`,
    // `RequestEBTxs` ↔ `MsgLeiosBlockTxsRequest` (bitmap-addressed),
    // `EBTxs` ↔ `MsgLeiosBlockTxs` (body list).
    AnnounceEBTxs(EndorserBlockId),
    RequestEBTxs(EndorserBlockId, BTreeMap<u16, u64>),
    EBTxs(EndorserBlockId, Vec<Arc<Transaction>>),

    // Vote propagation — bundle path used by `linear_leios.rs`.
    // Aggregates multiple votes for one voter into a single message;
    // sim-only, not in the CIP.
    AnnounceVotes(VoteBundleId),
    RequestVotes(VoteBundleId),
    Votes(Arc<VoteBundle>),

    // Vote propagation — per-vote path used by `con_rs.rs`.  One BLS
    // signature, one wire message; mirrors the CIP-0164 wire format.
    AnnounceVote(VoteId),
    RequestVote(VoteId),
    Vote(Arc<Vote>),
}

impl SimMessage for Message {
    fn protocol(&self) -> MiniProtocol {
        match self {
            Self::AnnounceTx(_) => MiniProtocol::Tx,
            Self::RequestTx(_) => MiniProtocol::Tx,
            Self::Tx(_) => MiniProtocol::Tx,

            Self::AnnounceRBHeader(_) => MiniProtocol::Block,
            Self::RequestRBHeader(_) => MiniProtocol::Block,
            Self::RBHeader(_, _, _) => MiniProtocol::Block,

            Self::AnnounceRB(_) => MiniProtocol::Block,
            Self::RequestRB(_) => MiniProtocol::Block,
            Self::RB(_) => MiniProtocol::Block,

            Self::AnnounceEB(_) => MiniProtocol::EB,
            Self::RequestEB(_) => MiniProtocol::EB,
            Self::EB(_) => MiniProtocol::EB,

            Self::AnnounceEBTxs(_) => MiniProtocol::EB,
            Self::RequestEBTxs(_, _) => MiniProtocol::EB,
            Self::EBTxs(_, _) => MiniProtocol::EB,

            Self::AnnounceVotes(_) => MiniProtocol::Vote,
            Self::RequestVotes(_) => MiniProtocol::Vote,
            Self::Votes(_) => MiniProtocol::Vote,

            Self::AnnounceVote(_) => MiniProtocol::Vote,
            Self::RequestVote(_) => MiniProtocol::Vote,
            Self::Vote(_) => MiniProtocol::Vote,
        }
    }

    fn bytes_size(&self) -> u64 {
        match self {
            Self::AnnounceTx(_) => 8,
            Self::RequestTx(_) => 8,
            Self::Tx(tx) => tx.bytes,

            Self::AnnounceRBHeader(_) => 8,
            Self::RequestRBHeader(_) => 8,
            Self::RBHeader(header, _, _) => header.bytes,

            Self::AnnounceRB(_) => 8,
            Self::RequestRB(_) => 8,
            Self::RB(rb) => rb.bytes(),

            Self::AnnounceEB(_) => 8,
            Self::RequestEB(_) => 8,
            Self::EB(eb) => eb.bytes,

            Self::AnnounceEBTxs(_) => 8,
            // CIP-0164 wire shape: EB point (40b) + bitmap entries
            // (2-byte u16 index + 8-byte u64 word = 10 bytes per
            // segment, plus a CBOR map overhead).
            Self::RequestEBTxs(_, bitmap) => 40 + 10 * bitmap.len() as u64,
            Self::EBTxs(_, txs) => {
                40 + txs.iter().map(|tx| tx.bytes).sum::<u64>()
            }

            Self::AnnounceVotes(_) => 8,
            Self::RequestVotes(_) => 8,
            Self::Votes(v) => v.bytes,

            Self::AnnounceVote(_) => 8,
            Self::RequestVote(_) => 8,
            Self::Vote(v) => v.bytes,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CpuTask {
    /// A transaction has been received and validated, and is ready to propagate
    TransactionValidated(NodeId, Arc<Transaction>),
    /// A ranking block has been generated and is ready to propagate
    RBBlockGenerated(RankingBlock, Option<(EndorserBlock, Vec<Arc<Transaction>>)>),
    /// An RB header has been received and validated, and ready to propagate
    RBHeaderValidated(NodeId, RankingBlockHeader, bool, bool),
    /// A ranking block has been received and validated, and is ready to propagate
    RBBlockValidated(Arc<RankingBlock>),
    /// An endorser block has been received, and its header has been validated.
    EBHeaderValidated(NodeId, Arc<EndorserBlock>),
    /// An endorser block has been received and validated, and is ready to propagate
    EBBlockValidated(Arc<EndorserBlock>, Timestamp),
    /// A bundle of votes has been generated and is ready to propagate
    /// (`linear_leios.rs` only — sim-only aggregation, not in the CIP)
    VTBundleGenerated(VoteBundle, Arc<EndorserBlock>),
    /// A bundle of votes has been received and validated, ready to propagate
    /// (`linear_leios.rs` only)
    VTBundleValidated(NodeId, Arc<VoteBundle>),
    /// A single CIP-0164 vote has been generated and is ready to propagate
    /// (`con_rs.rs` only — one BLS signature per CpuTask)
    VoteGenerated(Arc<Vote>),
    /// A single CIP-0164 vote has been received and validated, ready to propagate
    /// (`con_rs.rs` only)
    VoteValidated(NodeId, Arc<Vote>),
    /// A ranking block has been validated and is now being applied to
    /// ledger state — distinct from `RBBlockValidated` (block-body
    /// signature / structure check).  Scales with tx count because
    /// applying a real Cardano block walks every input + output.
    /// (`con_rs.rs` only — `linear_leios.rs` collapses validate+apply.)
    RBBlockApplied(Arc<RankingBlock>),
    /// An endorser block's closure has been validated and is now being
    /// applied to ledger state.  Gates mempool pruning of the EB's
    /// referenced txs.  (`con_rs.rs` only.)
    EBBlockApplied(Arc<EndorserBlock>),
}

impl SimCpuTask for CpuTask {
    fn name(&self) -> String {
        match self {
            Self::TransactionValidated(_, _) => "ValTX",
            Self::RBBlockGenerated(_, _) => "GenRB",
            Self::RBHeaderValidated(_, _, _, _) => "ValRH",
            Self::RBBlockValidated(_) => "ValRB",
            Self::EBHeaderValidated(_, _) => "ValEH",
            Self::EBBlockValidated(_, _) => "ValEB",
            Self::VTBundleGenerated(_, _) => "GenVote",
            Self::VTBundleValidated(_, _) => "ValVote",
            Self::VoteGenerated(_) => "GenVote",
            Self::VoteValidated(_, _) => "ValVote",
            Self::RBBlockApplied(_) => "AppRB",
            Self::EBBlockApplied(_) => "AppEB",
        }
        .to_string()
    }

    fn extra(&self) -> String {
        match self {
            Self::TransactionValidated(_, _) => "".to_string(),
            Self::RBBlockGenerated(_, _) => "".to_string(),
            Self::RBHeaderValidated(_, _, _, _) => "".to_string(),
            Self::RBBlockValidated(_) => "".to_string(),
            Self::EBHeaderValidated(_, _) => "".to_string(),
            Self::EBBlockValidated(_, _) => "".to_string(),
            Self::VTBundleGenerated(_, _) => "".to_string(),
            Self::VTBundleValidated(_, _) => "".to_string(),
            Self::VoteGenerated(_) => "".to_string(),
            Self::VoteValidated(_, _) => "".to_string(),
            Self::RBBlockApplied(_) => "".to_string(),
            Self::EBBlockApplied(_) => "".to_string(),
        }
    }

    fn times(&self, config: &CpuTimeConfig) -> Vec<Duration> {
        match self {
            Self::TransactionValidated(_, tx) => vec![
                config.tx_validation_constant + config.tx_validation_per_byte * tx.bytes as u32,
            ],
            Self::RBBlockGenerated(rb, eb) => {
                let mut rb_time = config.rb_generation + config.rb_body_validation_constant;
                let rb_bytes: u64 = rb.transactions.iter().map(|tx| tx.bytes).sum();
                rb_time += config.rb_validation_per_byte * (rb_bytes as u32);
                if let Some(endorsement) = &rb.endorsement {
                    let nodes = endorsement.votes.len();
                    rb_time += config.cert_generation_constant
                        + (config.cert_generation_per_node * nodes as u32);
                }
                let mut times = vec![rb_time];

                if let Some((eb, _)) = eb {
                    let mut eb_time = config.eb_generation + config.eb_body_validation_constant;
                    let eb_bytes: u64 = eb.txs.iter().map(|tx| tx.bytes).sum();
                    eb_time += config.eb_body_validation_per_byte * (eb_bytes as u32);
                    times.push(eb_time);
                }
                times
            }
            Self::RBHeaderValidated(_, _, _, _) => vec![config.rb_head_validation],
            Self::RBBlockValidated(rb) => {
                let mut time = config.rb_body_validation_constant;
                let bytes: u64 = rb.transactions.iter().map(|tx| tx.bytes).sum();
                time += config.rb_validation_per_byte * (bytes as u32);
                if let Some(endorsement) = &rb.endorsement {
                    let nodes = endorsement.votes.len();
                    time += config.cert_validation_constant
                        + (config.cert_validation_per_node * nodes as u32);
                }
                vec![time]
            }
            Self::EBHeaderValidated(_, _) => vec![config.eb_header_validation],
            Self::EBBlockValidated(eb, _) => {
                let mut time = config.eb_body_validation_constant;
                let bytes: u64 = eb.txs.iter().map(|tx| tx.bytes).sum();
                time += config.eb_body_validation_per_byte * (bytes as u32);
                vec![time]
            }
            Self::VTBundleGenerated(_, eb) => vec![
                config.vote_generation_constant
                    + (config.vote_generation_per_tx * eb.txs.len() as u32),
            ],
            Self::VTBundleValidated(_, _) => vec![config.vote_validation],
            // CIP-0164 per-vote: one BLS sign on the emit side; one
            // BLS pair-check on validation.  The per-tx EB-content
            // cost is absorbed by the EB-validation pipeline rather
            // than re-charged per vote.
            Self::VoteGenerated(_) => vec![config.vote_generation_constant],
            Self::VoteValidated(_, _) => vec![config.vote_validation],
            // Ledger-apply: scales by tx count (a real ledger walks
            // every input/output).  Distinct from body validation
            // (which is the signature/structure check that already
            // ran).  Minimal-but-nonzero default keeps the accounting
            // honest without skewing throughput; studies that need to
            // characterise the fork-rate-vs-apply-latency curve dial
            // this up.
            Self::RBBlockApplied(rb) => {
                let n_txs = rb.transactions.len() as u32;
                vec![config.rb_apply_constant + config.rb_apply_per_tx * n_txs]
            }
            Self::EBBlockApplied(eb) => {
                let n_txs = eb.txs.len() as u32;
                vec![config.eb_apply_constant + config.eb_apply_per_tx * n_txs]
            }
        }
    }
}

pub enum TimedEvent {
    TryVote(Arc<EndorserBlock>, Timestamp),
}
