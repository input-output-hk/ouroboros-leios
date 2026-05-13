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

use std::{sync::Arc, time::Duration};

use crate::{
    clock::Timestamp,
    config::{CpuTimeConfig, NodeId},
    model::{
        BlockId, EndorserBlockId, LinearEndorserBlock as EndorserBlock,
        LinearRankingBlock as RankingBlock, LinearRankingBlockHeader as RankingBlockHeader,
        Transaction, TransactionId, VoteBundle, VoteBundleId,
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

    // Vote propagation
    AnnounceVotes(VoteBundleId),
    RequestVotes(VoteBundleId),
    Votes(Arc<VoteBundle>),
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

            Self::AnnounceVotes(_) => MiniProtocol::Vote,
            Self::RequestVotes(_) => MiniProtocol::Vote,
            Self::Votes(_) => MiniProtocol::Vote,
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

            Self::AnnounceVotes(_) => 8,
            Self::RequestVotes(_) => 8,
            Self::Votes(v) => v.bytes,
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
    VTBundleGenerated(VoteBundle, Arc<EndorserBlock>),
    /// A bundle of votes has been received and validated, ready to propagate
    VTBundleValidated(NodeId, Arc<VoteBundle>),
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
        }
    }
}

pub enum TimedEvent {
    TryVote(Arc<EndorserBlock>, Timestamp),
}
