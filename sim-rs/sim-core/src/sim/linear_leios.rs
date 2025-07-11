use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
    time::Duration,
};

use rand::Rng as _;
use rand_chacha::ChaChaRng;

use crate::{
    clock::{Clock, Timestamp},
    config::{
        CpuTimeConfig, NodeConfiguration, NodeId, RelayStrategy, SimConfiguration,
        TransactionConfig,
    },
    events::EventTracker,
    model::{
        BlockId, EndorserBlockId, LinearEndorserBlock as EndorserBlock,
        LinearRankingBlock as RankingBlock, LinearRankingBlockHeader as RankingBlockHeader,
        Transaction, TransactionId,
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
    /// An endorser block has been received and validated, and is ready to propagate
    EBBlockValidated(NodeId, Arc<EndorserBlock>),
}

impl SimCpuTask for CpuTask {
    fn name(&self) -> String {
        match self {
            Self::TransactionValidated(_, _) => "ValTX",
            Self::RBBlockGenerated(_, _) => "GenRB",
            Self::RBHeaderValidated(_, _, _, _) => "ValRH",
            Self::RBBlockValidated(_) => "ValRB",
            Self::EBBlockValidated(_, _) => "ValEB",
        }
        .to_string()
    }

    fn extra(&self) -> String {
        match self {
            Self::TransactionValidated(_, _) => "".to_string(),
            Self::RBBlockGenerated(_, _) => "".to_string(),
            Self::RBHeaderValidated(_, _, _, _) => "".to_string(),
            Self::RBBlockValidated(_) => "".to_string(),
            Self::EBBlockValidated(_, _) => "".to_string(),
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
            Self::EBBlockValidated(_, eb) => {
                let mut time = config.eb_validation;
                let bytes: u64 = eb.txs.iter().map(|tx| tx.bytes).sum();
                time += config.rb_validation_per_byte * (bytes as u32);
                vec![time]
            }
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

#[derive(Default)]
struct NodeLeiosState {
    ebs: HashMap<EndorserBlockId, EndorserBlockView>,
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
            CpuTask::EBBlockValidated(from, eb) => self.finish_validating_eb(from, eb),
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
        let rb_ref = self.latest_rb_ref();
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
                let mut size = 0;
                // Fill with as many pending transactions as can fit
                while let Some((id, tx)) = self.praos.mempool.first_key_value() {
                    if size + tx.bytes > self.sim_config.max_block_size {
                        break;
                    }
                    size += tx.bytes;
                    let id = *id;
                    rb_transactions.push(self.praos.mempool.remove(&id).unwrap());
                }
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
            let mut size = 0;
            // Fill with as many pending transactions as can fit
            while let Some((id, tx)) = self.praos.mempool.first_key_value() {
                if size + tx.bytes > self.sim_config.max_eb_size {
                    break;
                }
                size += tx.bytes;
                let id = *id;
                eb_transactions.push(self.praos.mempool.remove(&id).unwrap());
            }
        }

        let parent = self.latest_rb_ref();

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
        for tx in &rb.transactions {
            self.praos.mempool.remove(&tx.id);
        }
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

        if has_eb {
            // TODO: freshest first
            self.queued.send_to(from, Message::RequestEB(eb_id));
            self.leios.ebs.insert(eb_id, EndorserBlockView::Requested);
        } else {
            self.leios.ebs.insert(eb_id, EndorserBlockView::Pending);
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

    fn latest_rb_ref(&self) -> Option<BlockId> {
        self.praos.blocks.last_key_value().map(|(id, _)| *id)
    }
}

// EB operations
impl LinearLeiosNode {
    fn finish_generating_eb(&mut self, eb: EndorserBlock) {
        let eb_id = eb.id();
        self.leios
            .ebs
            .insert(eb_id, EndorserBlockView::Received { eb: Arc::new(eb) });
        for peer in &self.consumers {
            self.queued.send_to(*peer, Message::AnnounceEB(eb_id));
        }
    }
    fn receive_announce_eb(&mut self, from: NodeId, id: EndorserBlockId) {
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
            .schedule_cpu_task(CpuTask::EBBlockValidated(from, eb));
    }

    fn finish_validating_eb(&mut self, from: NodeId, eb: Arc<EndorserBlock>) {
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
    }
}

// Ledger operations
impl LinearLeiosNode {
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

            // TODO: account for endorser blocks
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
