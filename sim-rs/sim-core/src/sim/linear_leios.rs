mod attackers;
pub use attackers::register_actors;
use rand_distr::Distribution;
use tokio::sync::mpsc;

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
        CpuTimeConfig, EBPropagationCriteria, LeiosVariant, MempoolSamplingStrategy,
        NodeBehaviours, NodeConfiguration, NodeId, RelayStrategy, SimConfiguration,
        TransactionConfig,
    },
    events::EventTracker,
    model::{
        BlockId, Endorsement, EndorserBlockId, LinearEndorserBlock as EndorserBlock,
        LinearRankingBlock as RankingBlock, LinearRankingBlockHeader as RankingBlockHeader,
        NoVoteReason, Transaction, TransactionId, VoteBundle, VoteBundleId,
    },
    sim::{
        MiniProtocol, NodeImpl, SimCpuTask, SimMessage,
        linear_leios::attackers::{EBWithholdingEvent, EBWithholdingSender},
        lottery,
    },
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
    RBBlockGenerated(RankingBlock, EndorserBlock, Vec<Arc<Transaction>>),
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
            Self::RBBlockGenerated(_, _, _) => "GenRB",
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
            Self::RBBlockGenerated(_, _, _) => "".to_string(),
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
            Self::RBBlockGenerated(_, _, _) => {
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

pub enum TimedEvent {
    TryVote(Arc<EndorserBlock>, Timestamp),
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

#[derive(Debug)]
enum EndorserBlockView {
    Pending,
    Requested,
    Received {
        eb: Arc<EndorserBlock>,
        seen: Timestamp,
        all_txs_seen: bool,
        validated: bool,
    },
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
    incomplete_onchain_ebs: HashSet<EndorserBlockId>,
    missing_txs: HashMap<TransactionId, Vec<EndorserBlockId>>,
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
    behaviours: NodeBehaviours,

    eb_withholding_sender: Option<EBWithholdingSender>,
    eb_withholding_event_source: Option<mpsc::UnboundedReceiver<EBWithholdingEvent>>,
}

type EventResult = super::EventResult<LinearLeiosNode>;

impl NodeImpl for LinearLeiosNode {
    type Message = Message;
    type Task = CpuTask;
    type TimedEvent = TimedEvent;
    type CustomEvent = EBWithholdingEvent;

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
            behaviours: config.behaviours.clone(),
            eb_withholding_sender: None,
            eb_withholding_event_source: None,
        }
    }

    fn custom_event_source(&mut self) -> Option<mpsc::UnboundedReceiver<Self::CustomEvent>> {
        self.eb_withholding_event_source.take()
    }

    fn handle_new_slot(&mut self, slot: u64) -> EventResult {
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
            CpuTask::RBBlockGenerated(rb, eb, withheld_txs) => {
                self.finish_generating_rb(rb, eb, withheld_txs)
            }
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

    fn handle_timed_event(&mut self, event: Self::TimedEvent) -> EventResult {
        match event {
            TimedEvent::TryVote(eb, seen) => self.vote_for_endorser_block(&eb, seen),
        }
        std::mem::take(&mut self.queued)
    }

    fn handle_custom_event(&mut self, event: Self::CustomEvent) -> EventResult {
        match event {
            EBWithholdingEvent::NewEB(eb, withheld_txs) => {
                self.receive_withheld_eb(eb, withheld_txs)
            }
            EBWithholdingEvent::DisseminateEB(eb, withheld_txs) => {
                self.disseminate_withheld_eb(eb, withheld_txs)
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

        let referenced_by_eb = self.acknowledge_tx(&tx);
        let added_to_mempool = self.try_add_tx_to_mempool(&tx);

        // If we added the TX to our mempool, we want to propagate it so our peers can as well.
        // If it was referenced by an EB, we want to propagate it so our peers have the full EB.
        // TODO: should send to producers instead (make configurable)
        if referenced_by_eb || added_to_mempool {
            for peer in &self.consumers {
                if *peer == from {
                    continue;
                }
                self.queued.send_to(*peer, Message::AnnounceTx(id));
            }
        }
    }

    fn has_tx(&self, tx_id: TransactionId) -> bool {
        matches!(self.txs.get(&tx_id), Some(TransactionView::Received(_)))
    }

    fn acknowledge_tx(&mut self, tx: &Transaction) -> bool {
        let Some(eb_ids) = self.leios.missing_txs.remove(&tx.id) else {
            return false;
        };
        for eb_id in eb_ids {
            self.try_validating_eb(eb_id);
        }
        true
    }
}

// Ranking block propagation
impl LinearLeiosNode {
    fn try_generate_rb(&mut self, slot: u64) {
        let Some(vrf) = self.run_vrf(self.sim_config.block_generation_probability) else {
            return;
        };

        let parent = self.latest_rb().map(|rb| rb.header.id);
        let endorsement = parent.and_then(|rb_id| {
            if rb_id.slot + self.sim_config.linear_diffuse_stage_length > slot {
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

            // We haven't necessarily finished validating this EB, or even received it and its contents.
            // That won't stop us from generating the endorsement, though it'll make us produce an empty block.
            if !self.is_eb_validated(*eb_id) {
                self.leios.incomplete_onchain_ebs.insert(*eb_id);
            }

            Some(Endorsement {
                eb: *eb_id,
                size_bytes: self.sim_config.sizes.cert(votes.len()),
                votes: votes.clone(),
            })
        });

        // If we haven't validated any EBs from the current chain, we have no way to tell whether
        // including a TX would introduce conflicts. So, don't include ANY TXs, just to be safe.
        let produce_empty_block = !self.leios.incomplete_onchain_ebs.is_empty();

        let mut rb_transactions = vec![];
        if !produce_empty_block && self.sim_config.praos_fallback {
            if let TransactionConfig::Mock(config) = &self.sim_config.transactions {
                // Add one transaction, the right size for the extra RB payload
                let tx = config.mock_tx(config.rb_size);
                self.tracker.track_transaction_generated(&tx, self.id);
                rb_transactions.push(Arc::new(tx));
            } else {
                self.sample_from_mempool(
                    &mut rb_transactions,
                    self.sim_config.max_block_size,
                    true,
                );
            }
        }

        let eb_id = EndorserBlockId {
            slot,
            pipeline: 0,
            producer: self.id,
        };

        let mut eb_transactions = vec![];
        let mut withheld_txs = vec![];
        if !produce_empty_block {
            // If we are performing a "withheld TX" attack, we will include a bunch of brand-new TXs in this EB.
            // They will get disseminated through the network at the same time as the EB.
            withheld_txs = self.generate_withheld_txs(slot);
            eb_transactions.extend(withheld_txs.iter().cloned());

            if let TransactionConfig::Mock(config) = &self.sim_config.transactions {
                // Add one transaction, the right size for the extra RB payload
                let extra_size =
                    config.eb_size - withheld_txs.iter().map(|tx| tx.bytes).sum::<u64>();
                if extra_size > 0 {
                    let tx = config.mock_tx(extra_size);
                    self.tracker.track_transaction_generated(&tx, self.id);
                    eb_transactions.push(Arc::new(tx));
                }
            } else {
                self.sample_from_mempool(&mut eb_transactions, self.sim_config.max_eb_size, false);
            }
        }

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
            .schedule_cpu_task(CpuTask::RBBlockGenerated(rb, eb, withheld_txs));
    }

    fn finish_generating_rb(
        &mut self,
        rb: RankingBlock,
        eb: EndorserBlock,
        withheld_txs: Vec<Arc<Transaction>>,
    ) {
        self.tracker.track_linear_rb_generated(&rb, &eb);
        self.publish_rb(Arc::new(rb), false);
        self.finish_generating_eb(eb, withheld_txs);
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
                // If we already have this RB's body,
                // let the requester know that it's ready to fetch.
                let have_body = matches!(rb, RankingBlockView::Received { .. });
                // If we already have the EB announced by this RB,
                // let the requester know that they can fetch it.
                // But if we are maliciously withholding the EB, do not let them know.
                let have_eb = matches!(
                    self.leios.ebs.get(&header.eb_announcement),
                    Some(EndorserBlockView::Received { .. })
                ) && !self.should_withhold_ebs();
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

                // Forget we ever saw that other block
                if let Some(RankingBlockView::Received { rb, .. }) =
                    self.praos.blocks.remove(old_block_id)
                {
                    if let Some(endorsement) = &rb.endorsement {
                        self.leios.incomplete_onchain_ebs.remove(&endorsement.eb);
                    }
                }
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

        // Get ready to fetch the announced EB (if we don't have it already)
        let eb_id = header.eb_announcement;
        if matches!(
            self.leios.ebs.get(&eb_id),
            Some(EndorserBlockView::Received { .. })
        ) {
            return;
        }

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
        if let Some(endorsement) = &rb.endorsement {
            if !self.is_eb_validated(endorsement.eb) {
                self.leios.incomplete_onchain_ebs.insert(endorsement.eb);
            }
        }

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
    fn finish_generating_eb(&mut self, eb: EndorserBlock, withheld_txs: Vec<Arc<Transaction>>) {
        let eb_id = eb.id();
        let eb = Arc::new(eb);
        self.leios.ebs.insert(
            eb_id,
            EndorserBlockView::Received {
                eb: eb.clone(),
                seen: self.clock.now(),
                all_txs_seen: true,
                validated: true,
            },
        );

        if self.should_withhold_ebs() {
            // We're an evil attacker, holding onto this EB until just long enough to collect votes.
            // Send it out-of-band to our evil buddies.
            self.share_new_withheld_eb(&eb, withheld_txs);
        } else {
            // We're a "well-behaved" node who will tell all our peers about this EB immediately.
            for peer in &self.consumers {
                self.queued.send_to(*peer, Message::AnnounceEB(eb_id));
                // If we were withholding some of the EB's transactions, start disseminating them now.
                for tx in &withheld_txs {
                    self.queued.send_to(*peer, Message::AnnounceTx(tx.id));
                }
            }
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
        if let Some(EndorserBlockView::Received { eb, .. }) = self.leios.ebs.get(&id) {
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
        if let Some(EndorserBlockView::Received { .. }) = self.leios.ebs.get(&eb.id()) {
            // already received this EB
            return;
        }
        let seen = self.clock.now();
        let missing_txs = if matches!(self.sim_config.variant, LeiosVariant::Linear) {
            vec![]
        } else {
            eb.txs
                .iter()
                .map(|tx| tx.id)
                .filter(|id| !self.has_tx(*id))
                .collect()
        };
        self.leios.ebs.insert(
            eb.id(),
            EndorserBlockView::Received {
                eb: eb.clone(),
                seen,
                all_txs_seen: missing_txs.is_empty(),
                validated: false,
            },
        );

        let should_propagate_now = match self.sim_config.linear_eb_propagation_criteria {
            EBPropagationCriteria::EbReceived => true,
            EBPropagationCriteria::TxsReceived => missing_txs.is_empty(),
            EBPropagationCriteria::FullyValid => false,
        };
        if should_propagate_now {
            for peer in &self.consumers {
                if *peer == from {
                    continue;
                }
                self.queued.send_to(*peer, Message::AnnounceEB(eb.id()));
            }
        }

        if missing_txs.is_empty() {
            self.queued
                .schedule_cpu_task(CpuTask::EBBlockValidated(eb, seen));
        } else {
            for tx_id in missing_txs {
                self.leios
                    .missing_txs
                    .entry(tx_id)
                    .or_default()
                    .push(eb.id());
            }
        }
    }

    fn try_validating_eb(&mut self, eb_id: EndorserBlockId) {
        let Some(EndorserBlockView::Received {
            eb,
            seen,
            all_txs_seen: false,
            validated: false,
        }) = self.leios.ebs.get(&eb_id)
        else {
            return;
        };
        let all_seen = eb.txs.iter().all(|tx| self.has_tx(tx.id));
        if all_seen {
            let eb = eb.clone();
            let seen = *seen;
            self.leios.ebs.insert(
                eb_id,
                EndorserBlockView::Received {
                    eb: eb.clone(),
                    seen,
                    all_txs_seen: true,
                    validated: false,
                },
            );
            if matches!(
                self.sim_config.linear_eb_propagation_criteria,
                EBPropagationCriteria::TxsReceived
            ) {
                // We have received all transactions, but haven't validated the entirety of the EB yet.
                // Propagate it now anyway.
                for peer in &self.consumers {
                    self.queued.send_to(*peer, Message::AnnounceEB(eb_id));
                }
            }
            self.queued
                .schedule_cpu_task(CpuTask::EBBlockValidated(eb, seen));
        }
    }

    fn finish_validating_eb(&mut self, eb: Arc<EndorserBlock>, seen: Timestamp) {
        if self.leios.incomplete_onchain_ebs.remove(&eb.id()) {
            self.remove_eb_txs_from_mempool(&eb);
        }
        let Some(EndorserBlockView::Received { validated, .. }) = self.leios.ebs.get_mut(&eb.id())
        else {
            panic!("how did we validate this EB without ever seeing it?");
        };
        *validated = true;
        if matches!(
            self.sim_config.linear_eb_propagation_criteria,
            EBPropagationCriteria::FullyValid
        ) {
            // We have received all transactions, but haven't validated the entirety of the EB yet.
            // Propagate it now anyway.
            for peer in &self.consumers {
                self.queued.send_to(*peer, Message::AnnounceEB(eb.id()));
            }
        }
        self.vote_for_endorser_block(&eb, seen);
    }

    fn is_eb_validated(&self, eb_id: EndorserBlockId) -> bool {
        matches!(
            self.leios.ebs.get(&eb_id),
            Some(EndorserBlockView::Received {
                validated: true,
                ..
            })
        )
    }
}

// EB withholding:
// an attack on Linear Leios where one or more stake pools deliberately wait to
// propagate an EB until there is just barely enough time for honest nodes to vote on it.
// This increases the odds that an honest RB producer won't have the parent RB's EB yet,
// meaning they will need to publish a completely empty RB.
impl LinearLeiosNode {
    // This is called during simulation setup.
    // It tells this node that it should withhold EBs,
    // and sets up a side channel with all other nodes performing the same attack.
    pub fn register_as_eb_withholder(
        &mut self,
        sender: EBWithholdingSender,
    ) -> mpsc::UnboundedSender<EBWithholdingEvent> {
        self.eb_withholding_sender = Some(sender);
        let (sink, source) = mpsc::unbounded_channel();
        self.eb_withholding_event_source = Some(source);
        sink
    }

    fn should_withhold_ebs(&self) -> bool {
        self.eb_withholding_sender.is_some()
    }

    fn share_new_withheld_eb(
        &mut self,
        eb: &Arc<EndorserBlock>,
        withheld_txs: Vec<Arc<Transaction>>,
    ) {
        let sender = self.eb_withholding_sender.as_ref().unwrap();
        sender.send(eb.clone(), withheld_txs);
    }

    fn receive_withheld_eb(&mut self, eb: Arc<EndorserBlock>, withheld_txs: Vec<Arc<Transaction>>) {
        self.leios.ebs.insert(
            eb.id(),
            EndorserBlockView::Received {
                eb: eb.clone(),
                seen: self.clock.now(),
                all_txs_seen: true,
                validated: true,
            },
        );
        for tx in withheld_txs {
            // Add the peer's withheld TXs to the list we know of,
            // but not to our mempools
            self.txs.insert(tx.id, TransactionView::Received(tx));
        }
        // If an attacker receives an EB over a side channel,
        // it will skip validation and will not disseminate it to peers.
        // It will, however, try to vote for the EB immediately.
        self.vote_for_endorser_block(&eb, self.clock.now());
    }

    fn disseminate_withheld_eb(
        &mut self,
        eb_id: EndorserBlockId,
        withheld_txs: Vec<TransactionId>,
    ) {
        for peer in &self.consumers {
            self.queued.send_to(*peer, Message::AnnounceEB(eb_id));
            for tx_id in &withheld_txs {
                self.queued.send_to(*peer, Message::AnnounceTx(*tx_id));
            }
        }
    }
}

// TX withholding:
// an attack where a stake pool generates EBs with previously unknown
// transactions, so that they cannot propagate in advance.
// We implement this by generating the transactions at the same time as the EB itself.
impl LinearLeiosNode {
    fn generate_withheld_txs(&mut self, slot: u64) -> Vec<Arc<Transaction>> {
        if !self.behaviours.withhold_txs {
            return vec![];
        }
        let withhold_tx_config = self.sim_config.attacks.late_tx.as_ref().unwrap();
        let slot_ts = Timestamp::from_secs(slot);
        if withhold_tx_config.start_time.is_some_and(|s| slot_ts < s) {
            return vec![];
        }
        if withhold_tx_config.stop_time.is_some_and(|s| slot_ts > s) {
            return vec![];
        }
        if !self.rng.random_bool(withhold_tx_config.probability) {
            return vec![];
        }

        let txs_to_generate = withhold_tx_config.txs_to_generate.sample(&mut self.rng) as u64;
        let mut txs = vec![];
        for _ in 0..txs_to_generate {
            let tx = match &self.sim_config.transactions {
                TransactionConfig::Real(cfg) => cfg.new_tx(&mut self.rng, None),
                TransactionConfig::Mock(cfg) => cfg.mock_tx(cfg.eb_size / txs_to_generate),
            };
            self.tracker.track_transaction_generated(&tx, self.id);
            let tx = Arc::new(tx);
            self.txs
                .insert(tx.id, TransactionView::Received(tx.clone()));
            txs.push(tx);
        }
        txs
    }
}

// Voting
impl LinearLeiosNode {
    fn vote_for_endorser_block(&mut self, eb: &Arc<EndorserBlock>, seen: Timestamp) {
        let equivocation_cutoff_time =
            Timestamp::from_secs(eb.slot) + (self.sim_config.header_diffusion_time * 3);
        if eb.producer != self.id && self.clock.now() < equivocation_cutoff_time {
            // If we haven't waited long enough to detect equivocations,
            // schedule voting later.
            self.queued.schedule_event(
                equivocation_cutoff_time,
                TimedEvent::TryVote(eb.clone(), seen),
            );
            return;
        }
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

        if self.sim_config.variant == LeiosVariant::LinearWithTxReferences {
            for tx in &eb.txs {
                if !self.has_tx(tx.id) {
                    // We won't vote for an EB if we don't have all the TXs it references
                    // NB: this should be redundant; in this variant, we wait for TXs before validating
                    return Err(NoVoteReason::MissingTX);
                }
            }
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
    fn try_add_tx_to_mempool(&mut self, tx: &Arc<Transaction>) -> bool {
        let ledger_state = self.resolve_ledger_state(self.latest_rb().map(|rb| rb.header.id));
        if ledger_state.spent_inputs.contains(&tx.input_id) {
            // This TX conflicts with something already on-chain
            return false;
        }

        if self
            .praos
            .mempool
            .values()
            .any(|t| t.input_id == tx.input_id)
        {
            // This TX conflicts with something already in the mempool
            return false;
        }
        self.praos.mempool.insert(tx.id, tx.clone());
        true
    }

    fn sample_from_mempool(
        &mut self,
        txs: &mut Vec<Arc<Transaction>>,
        max_size: u64,
        remove: bool,
    ) {
        let mut size = txs.iter().map(|tx| tx.bytes).sum::<u64>();
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
            if remove {
                txs.push(self.praos.mempool.remove(&id).unwrap());
            } else {
                txs.push(tx.clone());
            }
        }
    }

    fn remove_rb_txs_from_mempool(&mut self, rb: &RankingBlock) {
        let mut txs = rb.transactions.clone();
        if let Some(endorsement) = &rb.endorsement {
            if let Some(EndorserBlockView::Received { eb, .. }) =
                self.leios.ebs.get(&endorsement.eb)
            {
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
        let mut complete = true;
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
                match self.leios.ebs.get(&endorsement.eb) {
                    Some(EndorserBlockView::Received { eb, .. }) => {
                        for tx in &eb.txs {
                            if self.has_tx(tx.id) {
                                state.spent_inputs.insert(tx.input_id);
                            } else {
                                complete = false;
                            }
                        }
                    }
                    _ => {
                        // We haven't validated the EB yet, so we don't know the full ledger state
                        complete = false;
                    }
                }
            }
        }

        let state = Arc::new(state);
        if complete {
            self.ledger_states.insert(block_id, state.clone());
        }
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
