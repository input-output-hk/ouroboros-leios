use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
    time::Duration,
};

use rand::{Rng as _, seq::SliceRandom as _};
use rand_chacha::ChaChaRng;

use crate::{
    clock::{Clock, Timestamp},
    config::{
        CpuTimeConfig, MempoolSamplingStrategy, NodeConfiguration, NodeId, RelayStrategy,
        SimConfiguration, TransactionConfig,
    },
    events::EventTracker,
    model::{
        BlockId, Endorsement, EndorserBlockId, LinearEndorserBlock as EndorserBlock,
        LinearRankingBlock as RankingBlock, LinearRankingBlockHeader as RankingBlockHeader,
        NoVoteReason, Transaction, TransactionId, VoteBundle, VoteBundleId,
    },
    sim::{MiniProtocol, NodeImpl, SimCpuTask, SimMessage, lottery},
};

#[derive(Clone, Debug)]
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

pub enum CpuTask {
    /// A transaction has been received and validated, and is ready to propagate
    TransactionValidated(NodeId, Arc<Transaction>),
    /// A ranking block has been generated and is ready to propagate
    RBBlockGenerated(RankingBlock, EndorserBlock),
    /// An RB header has been received and validated, and ready to propagate
    RBHeaderValidated(NodeId, RankingBlockHeader, bool, bool),
    /// A ranking block has been received and validated, and is ready to propagate
    RBBlockValidated(Arc<RankingBlock>),
    /// An endorser block has been received, and its header has been validated. It is ready to propagate.
    EBHeaderValidated(NodeId, Arc<EndorserBlock>),
    /// An endorser block has been received and validated, and is ready to propagate
    EBBlockValidated(Arc<EndorserBlock>, Timestamp),
    /// A bundle of votes has been generated and is ready to propagate
    VTBundleGenerated(VoteBundle, Arc<EndorserBlock>),
    /// A bundle of votes has been received and validated, and is ready to propagate
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
            Self::TransactionValidated(_, _) => vec![config.tx_validation],
            Self::RBBlockGenerated(_, _) => {
                vec![config.rb_generation, config.eb_generation]
            }
            Self::RBHeaderValidated(_, _, _, _) => vec![config.rb_head_validation],
            Self::RBBlockValidated(rb) => {
                let mut time = config.rb_body_validation_constant;
                let bytes: u64 = rb.transactions.iter().map(|tx| tx.bytes).sum();
                time += config.rb_validation_per_byte * (bytes as u32);
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

enum TransactionView {
    Pending,
    Received(Arc<Transaction>),
}

enum RankingBlockView {
    HeaderPending,
    Pending {
        header: RankingBlockHeader,
        header_seen: Timestamp,
    },
    Requested {
        header: RankingBlockHeader,
        header_seen: Timestamp,
    },
    Received {
        rb: Arc<RankingBlock>,
        header_seen: Timestamp,
    },
}
impl RankingBlockView {
    fn header(&self) -> Option<&RankingBlockHeader> {
        match self {
            Self::HeaderPending => None,
            Self::Pending { header, .. } => Some(header),
            Self::Requested { header, .. } => Some(header),
            Self::Received { rb, .. } => Some(&rb.header),
        }
    }
    fn header_seen(&self) -> Option<Timestamp> {
        match self {
            Self::HeaderPending => None,
            Self::Pending { header_seen, .. } => Some(*header_seen),
            Self::Requested { header_seen, .. } => Some(*header_seen),
            Self::Received { header_seen, .. } => Some(*header_seen),
        }
    }
}

#[derive(Default)]
struct NodePraosState {
    mempool: BTreeMap<TransactionId, Arc<Transaction>>,
    peer_heads: BTreeMap<NodeId, u64>,
    blocks: BTreeMap<BlockId, RankingBlockView>,
    block_ids_by_slot: BTreeMap<u64, BlockId>,
}

enum EndorserBlockView {
    Pending,
    Requested,
    Received { eb: Arc<EndorserBlock> },
}

enum VoteBundleView {
    Requested,
    Received { votes: Arc<VoteBundle> },
}

#[derive(Default)]
struct NodeLeiosState {
    ebs: HashMap<EndorserBlockId, EndorserBlockView>,
    ebs_by_rb: HashMap<BlockId, EndorserBlockId>,
    eb_peer_announcements: HashMap<EndorserBlockId, Vec<NodeId>>,
    votes: HashMap<VoteBundleId, VoteBundleView>,
    votes_by_eb: HashMap<EndorserBlockId, BTreeMap<NodeId, usize>>,
    certified_ebs: HashSet<EndorserBlockId>,
}

#[derive(Clone, Default)]
struct LedgerState {
    spent_inputs: HashSet<u64>,
    seen_blocks: HashSet<BlockId>,
}

pub struct LinearLeiosNode {
    id: NodeId,
    sim_config: Arc<SimConfiguration>,
    queued: EventResult,
    tracker: EventTracker,
    rng: ChaChaRng,
    clock: Clock,
    stake: u64,
    consumers: Vec<NodeId>,
    txs: HashMap<TransactionId, TransactionView>,
    ledger_states: BTreeMap<BlockId, Arc<LedgerState>>,
    praos: NodePraosState,
    leios: NodeLeiosState,
}

type EventResult = super::EventResult<Message, CpuTask>;

impl NodeImpl for LinearLeiosNode {
    type Message = Message;
    type Task = CpuTask;

    fn new(
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        tracker: EventTracker,
        rng: ChaChaRng,
        clock: Clock,
    ) -> Self {
        Self {
            id: config.id,
            sim_config,
            queued: EventResult::default(),
            tracker,
            rng,
            clock,
            stake: config.stake,
            consumers: config.consumers.clone(),
            txs: HashMap::new(),
            ledger_states: BTreeMap::new(),
            praos: NodePraosState::default(),
            leios: NodeLeiosState::default(),
        }
    }

    fn handle_new_slot(&mut self, slot: u64) -> EventResult {
        self.process_certified_ebs(slot);
        self.try_generate_rb(slot);

        std::mem::take(&mut self.queued)
    }

    fn handle_new_tx(&mut self, tx: Arc<Transaction>) -> EventResult {
        self.generate_tx(tx);
        std::mem::take(&mut self.queued)
    }

    fn handle_message(&mut self, from: NodeId, msg: Self::Message) -> EventResult {
        match msg {
            // TX propagation
            Message::AnnounceTx(id) => self.receive_announce_tx(from, id),
            Message::RequestTx(id) => self.receive_request_tx(from, id),
            Message::Tx(tx) => self.receive_tx(from, tx),

            // RB header propagation
            Message::AnnounceRBHeader(id) => self.receive_announce_rb_header(from, id),
            Message::RequestRBHeader(id) => self.receive_request_rb_header(from, id),
            Message::RBHeader(header, has_body, has_eb) => {
                self.receive_rb_header(from, header, has_body, has_eb)
            }

            // RB body propagation
            Message::AnnounceRB(id) => self.receive_announce_rb(from, id),
            Message::RequestRB(id) => self.receive_request_rb(from, id),
            Message::RB(rb) => self.receive_rb(from, rb),

            // EB body propagation
            Message::AnnounceEB(id) => self.receive_announce_eb(from, id),
            Message::RequestEB(id) => self.receive_request_eb(from, id),
            Message::EB(rb) => self.receive_eb(from, rb),

            // Vote propagation
            Message::AnnounceVotes(id) => self.receive_announce_votes(from, id),
            Message::RequestVotes(id) => self.receive_request_votes(from, id),
            Message::Votes(votes) => self.receive_votes(from, votes),
        }
        std::mem::take(&mut self.queued)
    }

    fn handle_cpu_task(&mut self, task: Self::Task) -> EventResult {
        match task {
            CpuTask::TransactionValidated(from, tx) => self.propagate_tx(from, tx),
            CpuTask::RBBlockGenerated(rb, eb) => self.finish_generating_rb(rb, eb),
            CpuTask::RBHeaderValidated(from, header, has_body, has_eb) => {
                self.finish_validating_rb_header(from, header, has_body, has_eb)
            }
            CpuTask::RBBlockValidated(rb) => self.finish_validating_rb(rb),
            CpuTask::EBHeaderValidated(from, eb) => self.finish_validating_eb_header(from, eb),
            CpuTask::EBBlockValidated(eb, seen) => self.finish_validating_eb(eb, seen),
            CpuTask::VTBundleGenerated(votes, _) => self.finish_generating_vote_bundle(votes),
            CpuTask::VTBundleValidated(from, votes) => {
                self.finish_validating_vote_bundle(from, votes)
            }
        }
        std::mem::take(&mut self.queued)
    }
}

// Transaction propagation
impl LinearLeiosNode {
    fn receive_announce_tx(&mut self, from: NodeId, id: TransactionId) {
        if self.txs.get(&id).is_none_or(|t| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(t, TransactionView::Pending)
        }) {
            self.txs.insert(id, TransactionView::Pending);
            self.queued.send_to(from, Message::RequestTx(id));
        }
    }

    fn receive_request_tx(&mut self, from: NodeId, id: TransactionId) {
        if let Some(TransactionView::Received(tx)) = self.txs.get(&id) {
            self.tracker.track_transaction_sent(tx, self.id, from);
            self.queued.send_to(from, Message::Tx(tx.clone()));
        }
    }

    fn receive_tx(&mut self, from: NodeId, tx: Arc<Transaction>) {
        self.tracker
            .track_transaction_received(tx.id, from, self.id);
        self.queued
            .schedule_cpu_task(CpuTask::TransactionValidated(from, tx));
    }

    fn generate_tx(&mut self, tx: Arc<Transaction>) {
        self.tracker.track_transaction_generated(&tx, self.id);
        self.propagate_tx(self.id, tx);
    }

    fn propagate_tx(&mut self, from: NodeId, tx: Arc<Transaction>) {
        let id = tx.id;
        if self
            .txs
            .insert(id, TransactionView::Received(tx.clone()))
            .is_some_and(|tx| matches!(tx, TransactionView::Received(_)))
        {
            return;
        }
        let rb_ref = self.latest_rb().map(|rb| rb.header.id);
        let ledger_state = self.resolve_ledger_state(rb_ref);
        if ledger_state.spent_inputs.contains(&tx.input_id) {
            // Ignoring a TX which conflicts with something already onchain
            return;
        }
        if self
            .praos
            .mempool
            .values()
            .any(|mempool_tx| mempool_tx.input_id == tx.input_id)
        {
            // Ignoring a TX which conflicts with the current mempool contents.
            return;
        }
        self.praos.mempool.insert(tx.id, tx.clone());

        // TODO: should send to producers instead (make configurable)
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.queued.send_to(*peer, Message::AnnounceTx(id));
        }
    }
}

// Ranking block propagation
impl LinearLeiosNode {
    fn try_generate_rb(&mut self, slot: u64) {
        let Some(vrf) = self.run_vrf(self.sim_config.block_generation_probability) else {
            return;
        };

        let mut rb_transactions = vec![];
        if self.sim_config.praos_fallback {
            if let TransactionConfig::Mock(config) = &self.sim_config.transactions {
                // Add one transaction, the right size for the extra RB payload
                let tx = config.mock_tx(config.rb_size);
                self.tracker.track_transaction_generated(&tx, self.id);
                rb_transactions.push(Arc::new(tx));
            } else {
                self.sample_from_mempool(&mut rb_transactions, self.sim_config.max_block_size);
            }
        }

        let eb_id = EndorserBlockId {
            slot,
            pipeline: 0,
            producer: self.id,
        };
        let mut eb_transactions = vec![];
        if let TransactionConfig::Mock(config) = &self.sim_config.transactions {
            // Add one transaction, the right size for the extra RB payload
            let tx = config.mock_tx(config.eb_size);
            self.tracker.track_transaction_generated(&tx, self.id);
            eb_transactions.push(Arc::new(tx));
        } else {
            self.sample_from_mempool(&mut eb_transactions, self.sim_config.max_eb_size);
        }

        let parent = self.latest_rb().map(|rb| rb.header.id);
        let endorsement = parent.and_then(|rb_id| {
            if rb_id.slot
                + self.sim_config.linear_vote_stage_length
                + self.sim_config.linear_diffuse_stage_length
                > slot
            {
                // This RB was generated too quickly after another; hasn't been time to gather all the votes.
                // No endorsement.
                return None;
            }

            let eb_id = self.leios.ebs_by_rb.get(&rb_id)?;
            let votes = self.leios.votes_by_eb.get(eb_id)?;
            let total_votes = votes.values().copied().sum::<usize>();
            if (total_votes as u64) < self.sim_config.vote_threshold {
                // Not enough votes. No endorsement.
                return None;
            }

            Some(Endorsement {
                eb: *eb_id,
                size_bytes: self.sim_config.sizes.cert(votes.len()),
                votes: votes.clone(),
            })
        });

        let rb = RankingBlock {
            header: RankingBlockHeader {
                id: BlockId {
                    slot,
                    producer: self.id,
                },
                vrf,
                parent,
                bytes: self.sim_config.sizes.block_header,
                eb_announcement: eb_id,
            },
            transactions: rb_transactions,
            endorsement,
        };

        let eb = EndorserBlock {
            slot,
            producer: self.id,
            bytes: self.sim_config.sizes.linear_eb(&eb_transactions),
            txs: eb_transactions,
        };
        self.tracker.track_praos_block_lottery_won(rb.header.id);
        self.queued
            .schedule_cpu_task(CpuTask::RBBlockGenerated(rb, eb));
    }

    fn finish_generating_rb(&mut self, rb: RankingBlock, eb: EndorserBlock) {
        self.tracker.track_linear_rb_generated(&rb, &eb);
        self.publish_rb(Arc::new(rb), false);
        self.finish_generating_eb(eb);
    }

    fn publish_rb(&mut self, rb: Arc<RankingBlock>, already_sent_header: bool) {
        self.remove_rb_txs_from_mempool(&rb);
        for peer in &self.consumers {
            if self
                .praos
                .peer_heads
                .get(peer)
                .is_none_or(|&s| s < rb.header.id.slot)
            {
                let message = if already_sent_header {
                    Message::AnnounceRB(rb.header.id)
                } else {
                    Message::AnnounceRBHeader(rb.header.id)
                };
                self.queued.send_to(*peer, message);
                self.praos.peer_heads.insert(*peer, rb.header.id.slot);
            }
        }
        let header_seen = self
            .praos
            .blocks
            .get(&rb.header.id)
            .and_then(|rb| rb.header_seen())
            .unwrap_or(self.clock.now());
        self.leios
            .ebs_by_rb
            .insert(rb.header.id, rb.header.eb_announcement);
        self.praos
            .blocks
            .insert(rb.header.id, RankingBlockView::Received { rb, header_seen });
    }

    fn receive_announce_rb_header(&mut self, from: NodeId, id: BlockId) {
        let should_request = match self.praos.blocks.get(&id) {
            None => true,
            Some(RankingBlockView::HeaderPending) => {
                self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
            }
            _ => false,
        };
        if should_request {
            self.praos
                .blocks
                .insert(id, RankingBlockView::HeaderPending);
            self.queued.send_to(from, Message::RequestRBHeader(id));
        }
    }

    fn receive_request_rb_header(&mut self, from: NodeId, id: BlockId) {
        if let Some(rb) = self.praos.blocks.get(&id) {
            if let Some(header) = rb.header() {
                let have_body = matches!(rb, RankingBlockView::Received { .. });
                let have_eb = matches!(
                    self.leios.ebs.get(&header.eb_announcement),
                    Some(EndorserBlockView::Received { .. })
                );
                self.queued
                    .send_to(from, Message::RBHeader(header.clone(), have_body, have_eb));
            };
        };
    }

    fn receive_rb_header(
        &mut self,
        from: NodeId,
        header: RankingBlockHeader,
        has_body: bool,
        has_eb: bool,
    ) {
        self.queued
            .schedule_cpu_task(CpuTask::RBHeaderValidated(from, header, has_body, has_eb));
    }

    fn finish_validating_rb_header(
        &mut self,
        from: NodeId,
        header: RankingBlockHeader,
        has_body: bool,
        has_eb: bool,
    ) {
        if let Some(old_block_id) = self.praos.block_ids_by_slot.get(&header.id.slot) {
            // SLOT BATTLE!!! lower VRF wins
            if let Some(old_header) = self.praos.blocks.get(old_block_id).and_then(|b| b.header()) {
                if old_header.vrf <= header.vrf {
                    // We like our block better than this new one.
                    return;
                }
                self.praos.blocks.remove(old_block_id);
            }
        }
        self.praos
            .block_ids_by_slot
            .insert(header.id.slot, header.id);
        self.praos.blocks.insert(
            header.id,
            RankingBlockView::Pending {
                header: header.clone(),
                header_seen: self.clock.now(),
            },
        );

        let head = self.praos.peer_heads.entry(from).or_default();
        if *head < header.id.slot {
            *head = header.id.slot
        }
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.queued
                .send_to(*peer, Message::AnnounceRBHeader(header.id));
        }
        if has_body {
            self.queued.send_to(from, Message::RequestRB(header.id));
        }

        let eb_id = header.eb_announcement;

        let eb_peer_announcements = self.leios.eb_peer_announcements.entry(eb_id).or_default();
        if has_eb {
            eb_peer_announcements.push(from);
        }

        // TODO: freshest first
        let peers_to_request_from = match self.sim_config.relay_strategy {
            RelayStrategy::RequestFromFirst => eb_peer_announcements
                .first()
                .iter()
                .copied()
                .copied()
                .collect::<Vec<_>>(),
            RelayStrategy::RequestFromAll => eb_peer_announcements.clone(),
        };

        if peers_to_request_from.is_empty() {
            // nobody we know has this EB yet, wait for someone to announce it
            self.leios.ebs.insert(eb_id, EndorserBlockView::Pending);
        } else {
            for peer in peers_to_request_from {
                self.queued.send_to(peer, Message::RequestEB(eb_id));
            }
            self.leios.ebs.insert(eb_id, EndorserBlockView::Requested);
        }
    }

    fn receive_announce_rb(&mut self, from: NodeId, id: BlockId) {
        let (header, header_seen) = match self.praos.blocks.get(&id) {
            Some(RankingBlockView::Pending {
                header,
                header_seen,
                ..
            }) => (header.clone(), *header_seen),
            Some(RankingBlockView::Requested {
                header,
                header_seen,
            }) => {
                if self.sim_config.relay_strategy == RelayStrategy::RequestFromAll {
                    (header.clone(), *header_seen)
                } else {
                    return;
                }
            }
            _ => return,
        };

        self.praos.blocks.insert(
            id,
            RankingBlockView::Requested {
                header,
                header_seen,
            },
        );
        self.queued.send_to(from, Message::RequestRB(id));
    }

    fn receive_request_rb(&mut self, from: NodeId, id: BlockId) {
        if let Some(RankingBlockView::Received { rb, .. }) = self.praos.blocks.get(&id) {
            self.tracker.track_linear_rb_sent(rb, self.id, from);
            self.queued.send_to(from, Message::RB(rb.clone()));
        }
    }

    fn receive_rb(&mut self, from: NodeId, rb: Arc<RankingBlock>) {
        self.tracker.track_linear_rb_received(&rb, from, self.id);
        self.queued.schedule_cpu_task(CpuTask::RBBlockValidated(rb));
    }

    fn finish_validating_rb(&mut self, rb: Arc<RankingBlock>) {
        let header_seen = self
            .praos
            .blocks
            .get(&rb.header.id)
            .and_then(|rb| rb.header_seen())
            .unwrap_or(self.clock.now());
        self.praos.blocks.insert(
            rb.header.id,
            RankingBlockView::Received {
                rb: rb.clone(),
                header_seen,
            },
        );

        self.publish_rb(rb, true);
    }

    fn latest_rb(&self) -> Option<&Arc<RankingBlock>> {
        self.praos.blocks.iter().rev().find_map(|(_, rb)| {
            if let RankingBlockView::Received { rb, .. } = rb {
                Some(rb)
            } else {
                None
            }
        })
    }
}

// EB operations
impl LinearLeiosNode {
    fn finish_generating_eb(&mut self, eb: EndorserBlock) {
        let eb_id = eb.id();
        let eb = Arc::new(eb);
        self.leios
            .ebs
            .insert(eb_id, EndorserBlockView::Received { eb: eb.clone() });
        for peer in &self.consumers {
            self.queued.send_to(*peer, Message::AnnounceEB(eb_id));
        }
        self.vote_for_endorser_block(&eb, self.clock.now());
    }
    fn receive_announce_eb(&mut self, from: NodeId, id: EndorserBlockId) {
        self.leios
            .eb_peer_announcements
            .entry(id)
            .or_default()
            .push(from);
        let should_request = match self.leios.ebs.get(&id) {
            Some(EndorserBlockView::Pending) => true,
            Some(EndorserBlockView::Requested) => {
                self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
            }
            _ => false,
        };
        if should_request {
            // TODO: freshest first
            self.leios.ebs.insert(id, EndorserBlockView::Requested);
            self.queued.send_to(from, Message::RequestEB(id));
        }
    }

    fn receive_request_eb(&mut self, from: NodeId, id: EndorserBlockId) {
        if let Some(EndorserBlockView::Received { eb }) = self.leios.ebs.get(&id) {
            self.tracker.track_linear_eb_sent(eb, self.id, from);
            self.queued.send_to(from, Message::EB(eb.clone()));
        }
    }

    fn receive_eb(&mut self, from: NodeId, eb: Arc<EndorserBlock>) {
        self.tracker.track_eb_received(eb.id(), from, self.id);
        self.queued
            .schedule_cpu_task(CpuTask::EBHeaderValidated(from, eb));
    }

    fn finish_validating_eb_header(&mut self, from: NodeId, eb: Arc<EndorserBlock>) {
        if self
            .leios
            .ebs
            .insert(eb.id(), EndorserBlockView::Received { eb: eb.clone() })
            .is_some_and(|eb| matches!(eb, EndorserBlockView::Received { .. }))
        {
            return;
        }

        // TODO: sleep
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.queued.send_to(*peer, Message::AnnounceEB(eb.id()));
        }

        self.queued
            .schedule_cpu_task(CpuTask::EBBlockValidated(eb, self.clock.now()));
    }

    fn finish_validating_eb(&mut self, eb: Arc<EndorserBlock>, seen: Timestamp) {
        self.vote_for_endorser_block(&eb, seen);
    }

    fn process_certified_ebs(&mut self, slot: u64) {
        let Some(eb_creation_slot) = slot.checked_sub(
            self.sim_config.linear_vote_stage_length + self.sim_config.linear_diffuse_stage_length,
        ) else {
            return;
        };

        let Some(rb) = self.latest_rb() else {
            return;
        };

        if rb.header.id.slot != eb_creation_slot {
            return;
        }
        // The EB on the head of the chain has had enough time to get certified.

        let eb_id = rb.header.eb_announcement;
        if self.leios.certified_ebs.contains(&eb_id) {
            // This certified EB is eventually going on-chain.
            // Get its contents out of the mempool.
            if let Some(EndorserBlockView::Received { eb }) = self.leios.ebs.get(&eb_id) {
                self.remove_eb_txs_from_mempool(&eb.clone());
            };
        }
    }
}

// Voting
impl LinearLeiosNode {
    fn vote_for_endorser_block(&mut self, eb: &Arc<EndorserBlock>, seen: Timestamp) {
        if !self.try_vote_for_endorser_block(eb, seen) && self.sim_config.emit_conformance_events {
            self.tracker
                .track_linear_no_vote_generated(self.id, eb.id());
        }
    }

    fn try_vote_for_endorser_block(&mut self, eb: &Arc<EndorserBlock>, seen: Timestamp) -> bool {
        let vrf_wins = lottery::vrf_probabilities(self.sim_config.vote_probability)
            .filter_map(|f| self.run_vrf(f))
            .count();
        if vrf_wins == 0 {
            return false;
        }

        let id = VoteBundleId {
            slot: eb.slot,
            pipeline: 0,
            producer: self.id,
        };
        self.tracker.track_vote_lottery_won(id);

        if let Err(reason) = self.should_vote_for(eb, seen) {
            self.tracker
                .track_no_vote(eb.slot, 0, self.id, eb.id(), reason);
            return false;
        }

        let mut ebs = BTreeMap::new();
        ebs.insert(eb.id(), vrf_wins);
        let votes = VoteBundle {
            id,
            bytes: self.sim_config.sizes.vote_bundle(1),
            ebs,
        };
        self.queued
            .schedule_cpu_task(CpuTask::VTBundleGenerated(votes, eb.clone()));
        true
    }

    fn should_vote_for(&self, eb: &EndorserBlock, seen: Timestamp) -> Result<(), NoVoteReason> {
        let must_be_received_by =
            Timestamp::from_secs(eb.slot + self.sim_config.linear_vote_stage_length);
        if seen > must_be_received_by {
            // An EB must be received within L_vote slots of its creation.
            return Err(NoVoteReason::LateEB);
        }
        if self
            .latest_rb()
            .is_none_or(|rb| rb.header.eb_announcement != eb.id())
        {
            // We only vote for whichever EB we was referenced by the head of the current chain.
            return Err(NoVoteReason::WrongEB);
        }
        Ok(())
    }

    fn finish_generating_vote_bundle(&mut self, votes: VoteBundle) {
        self.tracker.track_votes_generated(&votes);
        self.count_votes(&votes);
        let id = votes.id;
        let votes = Arc::new(votes);
        self.leios
            .votes
            .insert(votes.id, VoteBundleView::Received { votes });
        for peer in &self.consumers {
            self.queued.send_to(*peer, Message::AnnounceVotes(id));
        }
    }

    fn receive_announce_votes(&mut self, from: NodeId, id: VoteBundleId) {
        let should_request = match self.leios.votes.get(&id) {
            None => true,
            Some(VoteBundleView::Requested) => {
                self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
            }
            _ => false,
        };
        if should_request {
            self.leios.votes.insert(id, VoteBundleView::Requested);
            self.queued.send_to(from, Message::RequestVotes(id));
        }
    }

    fn receive_request_votes(&mut self, from: NodeId, id: VoteBundleId) {
        if let Some(VoteBundleView::Received { votes }) = self.leios.votes.get(&id) {
            self.tracker.track_votes_sent(votes, self.id, from);
            self.queued.send_to(from, Message::Votes(votes.clone()));
        }
    }

    fn receive_votes(&mut self, from: NodeId, votes: Arc<VoteBundle>) {
        self.tracker.track_votes_received(&votes, from, self.id);
        self.queued
            .schedule_cpu_task(CpuTask::VTBundleValidated(from, votes));
    }

    fn finish_validating_vote_bundle(&mut self, from: NodeId, votes: Arc<VoteBundle>) {
        let id = votes.id;
        if self
            .leios
            .votes
            .insert(
                id,
                VoteBundleView::Received {
                    votes: votes.clone(),
                },
            )
            .is_some_and(|v| matches!(v, VoteBundleView::Received { .. }))
        {
            return;
        }
        self.count_votes(&votes);
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.queued.send_to(*peer, Message::AnnounceVotes(id));
        }
    }

    fn count_votes(&mut self, votes: &VoteBundle) {
        let vote_threshold = self.sim_config.vote_threshold as usize;
        for (eb_id, count) in votes.ebs.iter() {
            let all_eb_votes = self.leios.votes_by_eb.entry(*eb_id).or_default();
            let total_votes_before = all_eb_votes.values().sum::<usize>();
            *all_eb_votes.entry(votes.id.producer).or_default() += count;

            let total_votes_after = total_votes_before + count;
            if total_votes_before < vote_threshold && total_votes_after >= vote_threshold {
                // this EB is officially certified
                self.leios.certified_ebs.insert(*eb_id);
            }
        }
    }
}

// Ledger/mempool operations
impl LinearLeiosNode {
    fn sample_from_mempool(&mut self, txs: &mut Vec<Arc<Transaction>>, max_size: u64) {
        let mut size = 0;
        let mut candidates: Vec<_> = self.praos.mempool.keys().copied().collect();
        if matches!(
            self.sim_config.mempool_strategy,
            MempoolSamplingStrategy::Random
        ) {
            candidates.shuffle(&mut self.rng);
        } else {
            candidates.reverse();
        }

        // Fill with as many pending transactions as can fit
        while let Some(id) = candidates.pop() {
            let tx = self.praos.mempool.get(&id).unwrap();
            if size + tx.bytes > max_size {
                break;
            }
            size += tx.bytes;
            txs.push(self.praos.mempool.remove(&id).unwrap());
        }
    }

    fn remove_rb_txs_from_mempool(&mut self, rb: &RankingBlock) {
        let mut txs = rb.transactions.clone();
        if let Some(endorsement) = &rb.endorsement {
            if let Some(EndorserBlockView::Received { eb }) = self.leios.ebs.get(&endorsement.eb) {
                txs.extend(eb.txs.iter().cloned());
            }
        }
        self.remove_txs_from_mempool(&txs);
    }

    fn remove_eb_txs_from_mempool(&mut self, eb: &EndorserBlock) {
        self.remove_txs_from_mempool(&eb.txs);
    }

    fn remove_txs_from_mempool(&mut self, txs: &[Arc<Transaction>]) {
        let inputs = txs.iter().map(|tx| tx.input_id).collect::<HashSet<_>>();
        self.praos
            .mempool
            .retain(|_, tx| !inputs.contains(&tx.input_id));
    }

    fn resolve_ledger_state(&mut self, rb_ref: Option<BlockId>) -> Arc<LedgerState> {
        let Some(block_id) = rb_ref else {
            return Arc::new(LedgerState::default());
        };
        if let Some(state) = self.ledger_states.get(&block_id) {
            return state.clone();
        };

        let mut state = self
            .ledger_states
            .last_key_value()
            .map(|(_, v)| v.as_ref().clone())
            .unwrap_or_default();

        let mut block_queue = vec![block_id];
        while let Some(block_id) = block_queue.pop() {
            if !state.seen_blocks.insert(block_id) {
                continue;
            }
            let Some(RankingBlockView::Received { rb, .. }) = self.praos.blocks.get(&block_id)
            else {
                continue;
            };
            if let Some(parent) = rb.header.parent {
                block_queue.push(parent);
            }
            for tx in &rb.transactions {
                state.spent_inputs.insert(tx.input_id);
            }

            if let Some(endorsement) = &rb.endorsement {
                if let Some(EndorserBlockView::Received { eb }) =
                    self.leios.ebs.get(&endorsement.eb)
                {
                    for tx in &eb.txs {
                        state.spent_inputs.insert(tx.input_id);
                    }
                }
            }
        }

        let state = Arc::new(state);
        self.ledger_states.insert(block_id, state.clone());
        state
    }
}

// Common utilities
impl LinearLeiosNode {
    // Simulates the output of a VRF using this node's stake (if any).
    fn run_vrf(&mut self, success_rate: f64) -> Option<u64> {
        let target_vrf_stake = lottery::compute_target_vrf_stake(
            self.stake,
            self.sim_config.total_stake,
            success_rate,
        );
        let result = self.rng.random_range(0..self.sim_config.total_stake);
        if result < target_vrf_stake {
            Some(result)
        } else {
            None
        }
    }
}
