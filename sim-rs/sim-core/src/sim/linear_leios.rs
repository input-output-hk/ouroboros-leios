use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    sync::Arc,
    time::Duration,
};

use rand::Rng as _;
use rand_chacha::ChaChaRng;

use crate::{
    clock::Clock,
    config::{
        CpuTimeConfig, NodeConfiguration, NodeId, RelayStrategy, SimConfiguration,
        TransactionConfig,
    },
    events::EventTracker,
    model::{Block, BlockId, Transaction, TransactionId},
    sim::{MiniProtocol, NodeImpl, SimCpuTask, SimMessage, lottery},
};

#[derive(Clone, Debug)]
pub enum Message {
    // TX propagation
    AnnounceTx(TransactionId),
    RequestTx(TransactionId),
    Tx(Arc<Transaction>),

    // RB propagation
    AnnounceBlock(BlockId),
    RequestBlock(BlockId),
    Block(Arc<Block>),
}

impl SimMessage for Message {
    fn protocol(&self) -> MiniProtocol {
        match self {
            Self::AnnounceTx(_) => MiniProtocol::Tx,
            Self::RequestTx(_) => MiniProtocol::Tx,
            Self::Tx(_) => MiniProtocol::Tx,

            Self::AnnounceBlock(_) => MiniProtocol::Block,
            Self::RequestBlock(_) => MiniProtocol::Block,
            Self::Block(_) => MiniProtocol::Block,
        }
    }

    fn bytes_size(&self) -> u64 {
        match self {
            Self::AnnounceTx(_) => 8,
            Self::RequestTx(_) => 8,
            Self::Tx(tx) => tx.bytes,

            Self::AnnounceBlock(_) => 8,
            Self::RequestBlock(_) => 8,
            Self::Block(block) => block.bytes(),
        }
    }
}

pub enum CpuTask {
    /// A transaction has been received and validated, and is ready to propagate
    TransactionValidated(NodeId, Arc<Transaction>),
    /// A Praos block has been generated and is ready to propagate
    RBBlockGenerated(Block),
    /// A Praos block has been received and validated, and is ready to propagate
    RBBlockValidated(NodeId, Arc<Block>),
}

impl SimCpuTask for CpuTask {
    fn name(&self) -> String {
        match self {
            Self::TransactionValidated(_, _) => "ValTX",
            Self::RBBlockGenerated(_) => "GenRB",
            Self::RBBlockValidated(_, _) => "ValRB",
        }
        .to_string()
    }

    fn extra(&self) -> String {
        match self {
            Self::TransactionValidated(_, _) => "".to_string(),
            Self::RBBlockGenerated(_) => "".to_string(),
            Self::RBBlockValidated(_, _) => "".to_string(),
        }
    }

    fn times(&self, config: &CpuTimeConfig) -> Vec<Duration> {
        match self {
            Self::TransactionValidated(_, _) => vec![config.tx_validation],
            Self::RBBlockGenerated(_) => {
                let time = config.rb_generation;
                // TODO: account for endorsement
                vec![time]
            }
            Self::RBBlockValidated(_, rb) => {
                let mut time = config.rb_validation_constant;
                let bytes: u64 = rb.transactions.iter().map(|tx| tx.bytes).sum();
                time += config.rb_validation_per_byte * (bytes as u32);
                // TODO: account for endorsement
                vec![time]
            }
        }
    }
}

enum TransactionView {
    Pending,
    Received(Arc<Transaction>),
}

#[derive(Default)]
struct NodePraosState {
    mempool: BTreeMap<TransactionId, Arc<Transaction>>,
    peer_heads: BTreeMap<NodeId, u64>,
    blocks_seen: BTreeSet<BlockId>,
    blocks: BTreeMap<BlockId, Arc<Block>>,
    block_ids_by_slot: BTreeMap<u64, BlockId>,
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
    stake: u64,
    consumers: Vec<NodeId>,
    txs: HashMap<TransactionId, TransactionView>,
    ledger_states: BTreeMap<BlockId, Arc<LedgerState>>,
    praos: NodePraosState,
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
        _clock: Clock,
    ) -> Self {
        Self {
            id: config.id,
            sim_config,
            queued: EventResult::default(),
            tracker,
            rng,
            stake: config.stake,
            consumers: config.consumers.clone(),
            txs: HashMap::new(),
            ledger_states: BTreeMap::new(),
            praos: NodePraosState::default(),
        }
    }

    fn handle_new_slot(&mut self, slot: u64) -> EventResult {
        self.try_generate_block(slot);

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

            // Block propagation
            Message::AnnounceBlock(id) => self.receive_announce_block(from, id),
            Message::RequestBlock(id) => self.receive_request_block(from, id),
            Message::Block(block) => self.receive_block(from, block),
        }
        std::mem::take(&mut self.queued)
    }

    fn handle_cpu_task(&mut self, task: Self::Task) -> EventResult {
        match task {
            CpuTask::TransactionValidated(from, tx) => self.propagate_tx(from, tx),
            CpuTask::RBBlockGenerated(block) => self.finish_generating_block(block),
            CpuTask::RBBlockValidated(from, block) => self.finish_validating_block(from, block),
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
    fn try_generate_block(&mut self, slot: u64) {
        let Some(vrf) = self.run_vrf(self.sim_config.block_generation_probability) else {
            return;
        };

        // TODO: the actual linear leios bits

        let mut transactions = vec![];
        if self.sim_config.praos_fallback {
            if let TransactionConfig::Mock(config) = &self.sim_config.transactions {
                // Add one transaction, the right size for the extra RB payload
                let tx = config.mock_tx(config.rb_size);
                self.tracker.track_transaction_generated(&tx, self.id);
                transactions.push(Arc::new(tx));
            } else {
                let mut size = 0;
                // Fill with as many pending transactions as can fit
                while let Some((id, tx)) = self.praos.mempool.first_key_value() {
                    if size + tx.bytes > self.sim_config.max_block_size {
                        break;
                    }
                    size += tx.bytes;
                    let id = *id;
                    transactions.push(self.praos.mempool.remove(&id).unwrap());
                }
            }
        }

        let parent = self.latest_rb_ref();

        let block = Block {
            id: BlockId {
                slot,
                producer: self.id,
            },
            vrf,
            parent,
            header_bytes: self.sim_config.sizes.block_header,
            endorsement: None,
            transactions,
        };
        self.tracker.track_praos_block_lottery_won(&block);
        self.queued
            .schedule_cpu_task(CpuTask::RBBlockGenerated(block));
    }

    fn finish_generating_block(&mut self, block: Block) {
        self.tracker.track_praos_block_generated(&block);
        self.publish_block(Arc::new(block));
    }

    fn publish_block(&mut self, block: Arc<Block>) {
        for tx in &block.transactions {
            self.praos.mempool.remove(&tx.id);
        }
        for peer in &self.consumers {
            if self
                .praos
                .peer_heads
                .get(peer)
                .is_none_or(|&s| s < block.id.slot)
            {
                self.queued.send_to(*peer, Message::AnnounceBlock(block.id));
                self.praos.peer_heads.insert(*peer, block.id.slot);
            }
        }
        self.praos.block_ids_by_slot.insert(block.id.slot, block.id);
        self.praos.blocks.insert(block.id, block);
    }

    fn receive_announce_block(&mut self, from: NodeId, id: BlockId) {
        if self.praos.blocks_seen.insert(id) {
            self.queued.send_to(from, Message::RequestBlock(id));
        }
    }

    fn receive_request_block(&mut self, from: NodeId, id: BlockId) {
        if let Some(block) = self.praos.blocks.get(&id) {
            self.tracker.track_praos_block_sent(block, self.id, from);
            self.queued.send_to(from, Message::Block(block.clone()));
        }
    }

    fn receive_block(&mut self, from: NodeId, block: Arc<Block>) {
        self.tracker
            .track_praos_block_received(&block, from, self.id);
        self.queued
            .schedule_cpu_task(CpuTask::RBBlockValidated(from, block));
    }

    fn finish_validating_block(&mut self, from: NodeId, block: Arc<Block>) {
        if let Some(old_block_id) = self.praos.block_ids_by_slot.get(&block.id.slot) {
            // SLOT BATTLE!!! lower VRF wins
            if let Some(old_block) = self.praos.blocks.get(old_block_id) {
                if old_block.vrf <= block.vrf {
                    // We like our block better than this new one.
                    return;
                }
                self.praos.blocks.remove(old_block_id);
            }
        }
        self.praos.block_ids_by_slot.insert(block.id.slot, block.id);
        self.praos.blocks.insert(block.id, block.clone());

        let head = self.praos.peer_heads.entry(from).or_default();
        if *head < block.id.slot {
            *head = block.id.slot
        }
        self.publish_block(block);
    }

    fn latest_rb_ref(&self) -> Option<BlockId> {
        self.praos.blocks.last_key_value().map(|(id, _)| *id)
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
            let Some(block) = self.praos.blocks.get(&block_id) else {
                continue;
            };
            if let Some(parent) = block.parent {
                block_queue.push(parent);
            }
            for tx in &block.transactions {
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
