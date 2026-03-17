use std::{
    collections::{BinaryHeap, HashMap, HashSet},
    sync::{Arc, atomic::Ordering, mpsc as std_mpsc},
    time::Duration,
};

use anyhow::Result;
use rand::{Rng, RngCore};
use rand_chacha::{ChaChaRng, rand_core::SeedableRng};
use rand_distr::Distribution;
use rayon::prelude::*;
use tokio_util::sync::CancellationToken;
use tracing::trace;

use crate::{
    clock::{Clock, ClockCoordinator, FutureEvent, Timestamp, timestamp::AtomicTimestamp},
    config::{LeiosVariant, NodeId, RealTransactionConfig, SimConfiguration, TransactionConfig},
    events::EventTracker,
    model::{CpuTaskId, Transaction},
    network::connection::Connection,
    sim::{
        MiniProtocol, NodeImpl, SimCpuTask, SimMessage as _,
        cpu::{CpuTaskQueue, Subtask},
        leios::LeiosNode,
        linear_leios::LinearLeiosNode,
        stracciatella::StracciatellaLeiosNode,
    },
};

// Duplicated from driver.rs (private types)

enum NodeEvent<T> {
    NewSlot(u64),
    CpuSubtaskCompleted(Subtask),
    Other(T),
}

struct CpuTaskWrapper<Task: SimCpuTask> {
    task_type: Task,
    start_time: Timestamp,
    cpu_time: Duration,
}

/// Per-node state in the sequential engine.
struct NodeState<N: NodeImpl> {
    node: N,
    id: NodeId,
    /// Local index within this shard's node vec (may differ from id.to_inner() in multi-shard).
    local_idx: usize,
    name: String,
    trace: bool,
    cpu: CpuTaskQueue<CpuTaskWrapper<N::Task>>,
    tracker: EventTracker,
    config: Arc<SimConfiguration>,
}

/// Directed link key for connection lookup.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Link {
    from: NodeId,
    to: NodeId,
}

/// Events in the global priority queue.
enum GlobalEvent<N: NodeImpl> {
    NodeTimed {
        node_idx: usize,
        event: NodeEvent<N::TimedEvent>,
    },
    NetworkDelivery(Link),
    TxGeneration,
    SlotBoundary { slot: u64 },
}

/// Work item for the parallel compute phase.
enum WorkItem<N: NodeImpl> {
    NewSlot(u64),
    CpuSubtaskCompleted(Subtask),
    TimedEvent(N::TimedEvent),
    Message(NodeId, N::Message),
    NewTx(Arc<Transaction>),
}

/// Side effects from processing a batch of work items for one node.
struct BatchNodeOutput<N: NodeImpl> {
    messages: Vec<(NodeId, NodeId, u64, MiniProtocol, N::Message)>,
    new_events: Vec<FutureEvent<GlobalEvent<N>>>,
}

impl<N: NodeImpl> Default for BatchNodeOutput<N> {
    fn default() -> Self {
        Self {
            messages: Vec::new(),
            new_events: Vec::new(),
        }
    }
}

/// Minimum batch size to use rayon parallelism.
const PARALLEL_THRESHOLD: usize = 32;

/// Cross-shard message sent between sequential shards.
struct CrossShardMsg<M> {
    from: NodeId,
    to: NodeId,
    protocol: MiniProtocol,
    body: M,
    bytes: u64,
    send_time: Timestamp,
}

/// CMB peer shard reference for ceiling computation.
struct PeerShardInfo {
    time: Arc<AtomicTimestamp>,
    min_latency: Duration,
}

/// Transaction generation state.
struct TxGenerator {
    rng: ChaChaRng,
    config: Option<RealTransactionConfig>,
    node_weights: Vec<(usize, u64)>,
    total_weight: u64,
    shard_count: usize,
    tx_conflict_fractions: Vec<Option<f64>>,
}

impl TxGenerator {
    fn new(
        rng: ChaChaRng,
        config: &SimConfiguration,
        node_indices: &HashMap<NodeId, usize>,
    ) -> Self {
        let real_config = match &config.transactions {
            TransactionConfig::Real(c) => Some(c.clone()),
            _ => None,
        };

        let mut cumulative = 0u64;
        let mut node_weights = Vec::new();
        let mut tx_conflict_fractions = vec![None; node_indices.len()];

        for node_config in &config.nodes {
            let Some(&idx) = node_indices.get(&node_config.id) else {
                continue;
            };
            if idx < tx_conflict_fractions.len() {
                tx_conflict_fractions[idx] = node_config.tx_conflict_fraction;
            }
            let weight = node_config
                .tx_generation_weight
                .unwrap_or(if node_config.stake > 0 { 0 } else { 1 });
            if weight > 0 {
                cumulative += weight;
                node_weights.push((idx, cumulative));
            }
        }

        Self {
            rng,
            config: real_config,
            node_weights,
            total_weight: cumulative,
            shard_count: config.shard_count,
            tx_conflict_fractions,
        }
    }

    fn first_event_time(&self) -> Option<Timestamp> {
        let config = self.config.as_ref()?;
        if self.total_weight == 0 {
            return None;
        }
        Some(config.start_time.unwrap_or(Timestamp::zero()))
    }

    fn generate(
        &mut self,
        now: Timestamp,
    ) -> Option<(usize, Arc<Transaction>, Option<Timestamp>)> {
        let config = self.config.as_ref()?;
        if self.total_weight == 0 {
            return None;
        }

        let choice = self.rng.random_range(0..self.total_weight);
        let idx = match self
            .node_weights
            .binary_search_by_key(&choice, |(_, w)| *w)
        {
            Ok(i) => self.node_weights[i].0,
            Err(i) => self.node_weights[i].0,
        };

        let tx = config.new_tx(&mut self.rng, self.tx_conflict_fractions.get(idx).copied().flatten());

        let millis_until_tx =
            config.frequency_ms.sample(&mut self.rng) as u64 * self.shard_count as u64;
        let next_at = now + Duration::from_millis(millis_until_tx);

        let next_time = if config.stop_time.is_some_and(|t| next_at > t) {
            None
        } else {
            Some(next_at)
        };

        Some((idx, Arc::new(tx), next_time))
    }
}

/// The sequential discrete event simulation engine.
/// Supports both single-shard and multi-shard (CMB) operation.
pub(super) struct SequentialSimulation<N: NodeImpl> {
    nodes: Vec<NodeState<N>>,
    node_indices: HashMap<NodeId, usize>,
    connections: HashMap<Link, Connection<MiniProtocol, N::Message>>,
    event_queue: BinaryHeap<FutureEvent<GlobalEvent<N>>>,
    pending_deliveries: HashSet<Link>,
    tx_generator: TxGenerator,
    tracker: EventTracker,
    config: Arc<SimConfiguration>,
    shared_time: Arc<AtomicTimestamp>,
    /// Whether this shard handles slot boundaries and termination.
    is_primary: bool,
    /// This shard's index (for cross-shard routing).
    shard_index: usize,
    /// Cross-shard routing: maps NodeId to shard index.
    shard_lookup: Option<Arc<HashMap<NodeId, usize>>>,
    /// Senders for cross-shard messages, indexed by target shard.
    cross_shard_tx: Vec<std_mpsc::Sender<CrossShardMsg<N::Message>>>,
    /// Receiver for incoming cross-shard messages.
    cross_shard_rx: Option<std_mpsc::Receiver<CrossShardMsg<N::Message>>>,
    /// CMB peer shard info for ceiling computation.
    peer_shards: Vec<PeerShardInfo>,
}

impl<N: NodeImpl> SequentialSimulation<N> {
    /// Run the simulation using BSP batch processing with rayon parallelism.
    pub(super) fn run(mut self, token: CancellationToken) -> Result<()>
    where
        N: Send,
        N::Message: Send,
        N::Task: Send,
        N::TimedEvent: Send,
    {
        let num_nodes = self.nodes.len();
        let mut per_node_work: Vec<Vec<WorkItem<N>>> = (0..num_nodes).map(|_| Vec::new()).collect();

        loop {
            if token.is_cancelled() {
                break;
            }

            // === Drain incoming cross-shard messages ===
            if let Some(rx) = &self.cross_shard_rx {
                while let Ok(msg) = rx.try_recv() {
                    let link = Link {
                        from: msg.from,
                        to: msg.to,
                    };
                    if let Some(connection) = self.connections.get_mut(&link) {
                        connection.send(msg.body, msg.bytes, msg.protocol, msg.send_time);
                        if !self.pending_deliveries.contains(&link) {
                            if let Some(next_arrival) = connection.next_arrival_time() {
                                self.pending_deliveries.insert(link.clone());
                                self.event_queue.push(FutureEvent(
                                    next_arrival,
                                    GlobalEvent::NetworkDelivery(link),
                                ));
                            }
                        }
                    }
                }
            }

            // === Check next event timestamp ===
            let Some(FutureEvent(timestamp, _)) = self.event_queue.peek() else {
                // No events — if we have peers, yield and retry (they may send us messages)
                if !self.peer_shards.is_empty() {
                    std::thread::yield_now();
                    continue;
                }
                break;
            };
            let timestamp = *timestamp;

            // === CMB ceiling check ===
            if !self.peer_shards.is_empty() {
                let ceiling = self
                    .peer_shards
                    .iter()
                    .map(|p| p.time.load(Ordering::Acquire) + p.min_latency)
                    .min()
                    .unwrap_or(Timestamp::max());

                if timestamp > ceiling {
                    // Can't advance past ceiling — publish our time up to ceiling
                    let current = self.shared_time.load(Ordering::Acquire);
                    if ceiling > current {
                        self.shared_time.store(ceiling, Ordering::Release);
                    }
                    std::thread::yield_now();
                    continue;
                }
            }

            self.shared_time.store(timestamp, Ordering::Release);

            // === Pop all events at this timestamp ===
            let mut total_node_work = 0usize;
            let mut done = false;

            while self
                .event_queue
                .peek()
                .is_some_and(|e| e.0 == timestamp)
            {
                let FutureEvent(_, event) = self.event_queue.pop().unwrap();
                match event {
                    GlobalEvent::NodeTimed { node_idx, event } => {
                        per_node_work[node_idx].push(match event {
                            NodeEvent::NewSlot(slot) => WorkItem::NewSlot(slot),
                            NodeEvent::CpuSubtaskCompleted(s) => WorkItem::CpuSubtaskCompleted(s),
                            NodeEvent::Other(e) => WorkItem::TimedEvent(e),
                        });
                        total_node_work += 1;
                    }
                    GlobalEvent::NetworkDelivery(link) => {
                        self.pending_deliveries.remove(&link);
                        let connection = self.connections.get_mut(&link).unwrap();
                        let messages = connection.recv_many(timestamp);
                        if let Some(next_arrival) = connection.next_arrival_time() {
                            self.pending_deliveries.insert(link.clone());
                            self.event_queue.push(FutureEvent(
                                next_arrival,
                                GlobalEvent::NetworkDelivery(link.clone()),
                            ));
                        }
                        let node_idx = self.node_indices[&link.to];
                        for (msg, _) in messages {
                            per_node_work[node_idx].push(WorkItem::Message(link.from, msg));
                            total_node_work += 1;
                        }
                    }
                    GlobalEvent::TxGeneration => {
                        if let Some((node_idx, tx, next_time)) =
                            self.tx_generator.generate(timestamp)
                        {
                            if let Some(t) = next_time {
                                self.event_queue
                                    .push(FutureEvent(t, GlobalEvent::TxGeneration));
                            }
                            per_node_work[node_idx].push(WorkItem::NewTx(tx));
                            total_node_work += 1;
                        }
                    }
                    GlobalEvent::SlotBoundary { slot } => {
                        if self.is_primary {
                            self.tracker.track_global_slot(slot);
                        }
                        let next_slot = slot + 1;
                        if self.config.slots == Some(next_slot) {
                            done = true;
                            token.cancel();
                        } else {
                            self.event_queue.push(FutureEvent(
                                Timestamp::zero() + Duration::from_secs(next_slot),
                                GlobalEvent::SlotBoundary { slot: next_slot },
                            ));
                        }
                    }
                }
            }

            if done {
                break;
            }

            if total_node_work == 0 {
                continue;
            }

            // === Compute — process node work items ===
            if total_node_work >= PARALLEL_THRESHOLD {
                let outputs: Vec<BatchNodeOutput<N>> = self
                    .nodes
                    .par_iter_mut()
                    .zip(per_node_work.par_iter_mut())
                    .filter(|(_, work)| !work.is_empty())
                    .map(|(node_state, work)| {
                        process_node_batch(node_state, work.drain(..).collect(), timestamp)
                    })
                    .collect();

                for output in outputs {
                    self.apply_batch_output(output, timestamp);
                }
            } else {
                for node_idx in 0..num_nodes {
                    if per_node_work[node_idx].is_empty() {
                        continue;
                    }
                    let work: Vec<_> = per_node_work[node_idx].drain(..).collect();
                    let output =
                        process_node_batch(&mut self.nodes[node_idx], work, timestamp);
                    self.apply_batch_output(output, timestamp);
                }
            }

            for work in &mut per_node_work {
                work.clear();
            }
        }

        Ok(())
    }

    /// Apply the side effects from a batch of node processing.
    fn apply_batch_output(&mut self, output: BatchNodeOutput<N>, timestamp: Timestamp) {
        for (from_id, to, bytes, protocol, msg) in output.messages {
            // Check if this is a cross-shard message
            if let Some(lookup) = &self.shard_lookup {
                let target_shard = lookup[&to];
                if target_shard != self.shard_index {
                    // Cross-shard: send via channel
                    let _ = self.cross_shard_tx[target_shard].send(CrossShardMsg {
                        from: from_id,
                        to,
                        protocol,
                        body: msg,
                        bytes,
                        send_time: timestamp,
                    });
                    continue;
                }
            }

            // Intra-shard: route through local connection
            let link = Link { from: from_id, to };
            if let Some(connection) = self.connections.get_mut(&link) {
                connection.send(msg, bytes, protocol, timestamp);
                if !self.pending_deliveries.contains(&link) {
                    if let Some(next_arrival) = connection.next_arrival_time() {
                        self.pending_deliveries.insert(link.clone());
                        self.event_queue.push(FutureEvent(
                            next_arrival,
                            GlobalEvent::NetworkDelivery(link),
                        ));
                    }
                }
            }
        }

        for event in output.new_events {
            self.event_queue.push(event);
        }
    }
}

/// Process a batch of work items for a single node.
fn process_node_batch<N: NodeImpl>(
    node_state: &mut NodeState<N>,
    work: Vec<WorkItem<N>>,
    timestamp: Timestamp,
) -> BatchNodeOutput<N> {
    let mut output = BatchNodeOutput::default();
    let node_idx = node_state.local_idx;
    let from_id = node_state.id;

    for item in work {
        let result = match item {
            WorkItem::NewSlot(slot) => {
                if node_state.config.emit_conformance_events && slot > 0 {
                    node_state.tracker.track_slot(node_state.id, slot - 1);
                }
                output.new_events.push(FutureEvent(
                    timestamp + Duration::from_secs(1),
                    GlobalEvent::NodeTimed {
                        node_idx,
                        event: NodeEvent::NewSlot(slot + 1),
                    },
                ));
                node_state.node.handle_new_slot(slot)
            }
            WorkItem::CpuSubtaskCompleted(subtask) => {
                let task_id = CpuTaskId {
                    node: node_state.id,
                    index: subtask.task_id,
                };
                let (finished_task, next_subtask) = node_state.cpu.complete_subtask(subtask);

                if let Some((subtask, task)) = next_subtask {
                    let task_type = task.task_type.name();
                    node_state.tracker.track_cpu_subtask_started(
                        CpuTaskId {
                            node: node_state.id,
                            index: subtask.task_id,
                        },
                        task_type,
                        subtask.subtask_id,
                        subtask.duration,
                    );
                    output.new_events.push(FutureEvent(
                        timestamp + subtask.duration,
                        GlobalEvent::NodeTimed {
                            node_idx,
                            event: NodeEvent::CpuSubtaskCompleted(subtask),
                        },
                    ));
                }

                let Some(task) = finished_task else {
                    continue;
                };
                let wall_time = timestamp - task.start_time;
                node_state.tracker.track_cpu_task_finished(
                    task_id,
                    task.task_type.name(),
                    task.cpu_time,
                    wall_time,
                    task.task_type.extra(),
                );
                node_state.node.handle_cpu_task(task.task_type)
            }
            WorkItem::TimedEvent(event) => node_state.node.handle_timed_event(event),
            WorkItem::Message(from, msg) => node_state.node.handle_message(from, msg),
            WorkItem::NewTx(tx) => node_state.node.handle_new_tx(tx),
        };

        for (to, msg) in result.messages {
            if node_state.trace {
                trace!(
                    "node {} sent msg of size {} to node {to}",
                    node_state.name,
                    msg.bytes_size()
                );
            }
            let bytes = msg.bytes_size();
            let protocol = msg.protocol();
            output.messages.push((from_id, to, bytes, protocol, msg));
        }

        for task in result.tasks {
            schedule_cpu_task_batch(node_state, &mut output, node_idx, timestamp, task);
        }

        for (time, event) in result.timed_events {
            output.new_events.push(FutureEvent(
                time,
                GlobalEvent::NodeTimed {
                    node_idx,
                    event: NodeEvent::Other(event),
                },
            ));
        }
    }

    output
}

/// Schedule a CPU task within the batch processing context.
fn schedule_cpu_task_batch<N: NodeImpl>(
    node_state: &mut NodeState<N>,
    output: &mut BatchNodeOutput<N>,
    node_idx: usize,
    now: Timestamp,
    task: N::Task,
) {
    let cpu_times = task.times(&node_state.config.cpu_times);
    let task = CpuTaskWrapper {
        task_type: task,
        start_time: now,
        cpu_time: cpu_times.iter().sum(),
    };
    let name = task.task_type.name();
    let subtask_count = cpu_times.len();
    let (task_id, subtasks) = node_state.cpu.schedule_task(task, cpu_times);
    node_state.tracker.track_cpu_task_scheduled(
        CpuTaskId {
            node: node_state.id,
            index: task_id,
        },
        name.clone(),
        subtask_count,
    );
    for subtask in subtasks {
        node_state.tracker.track_cpu_subtask_started(
            CpuTaskId {
                node: node_state.id,
                index: subtask.task_id,
            },
            name.clone(),
            subtask.subtask_id,
            subtask.duration,
        );
        output.new_events.push(FutureEvent(
            now + subtask.duration,
            GlobalEvent::NodeTimed {
                node_idx,
                event: NodeEvent::CpuSubtaskCompleted(subtask),
            },
        ));
    }
}

// ─── Builder functions ───────────────────────────────────────────────────────

/// Trait for type-erased sequential simulation running.
pub(crate) trait SequentialRunner: Send {
    fn run(self: Box<Self>, token: CancellationToken) -> Result<()>;
}

impl<N: NodeImpl + Send> SequentialRunner for SequentialSimulation<N>
where
    N::Message: Send + Sync,
    N::Task: Send + Sync,
    N::TimedEvent: Send + Sync,
    N::CustomEvent: Send,
{
    fn run(self: Box<Self>, token: CancellationToken) -> Result<()> {
        (*self).run(token)
    }
}

/// Multi-shard runner: spawns each shard on its own OS thread.
struct MultiShardRunner<N: NodeImpl> {
    shards: Vec<SequentialSimulation<N>>,
}

impl<N: NodeImpl + Send + 'static> SequentialRunner for MultiShardRunner<N>
where
    N::Message: Send + Sync,
    N::Task: Send + Sync,
    N::TimedEvent: Send + Sync,
    N::CustomEvent: Send,
{
    fn run(self: Box<Self>, token: CancellationToken) -> Result<()> {
        std::thread::scope(|s| {
            let handles: Vec<_> = self
                .shards
                .into_iter()
                .map(|shard| {
                    let token = token.clone();
                    s.spawn(move || shard.run(token))
                })
                .collect();

            let mut first_error = None;
            for handle in handles {
                if let Err(e) = handle.join().unwrap() {
                    if first_error.is_none() {
                        first_error = Some(e);
                    }
                }
            }
            match first_error {
                Some(e) => Err(e),
                None => Ok(()),
            }
        })
    }
}

/// Build a sequential DES engine for the given config.
/// Returns a single-shard or multi-shard runner depending on shard_count.
pub(super) fn build(
    config: Arc<SimConfiguration>,
    tracker: EventTracker,
    clock: Clock,
    shared_time: Arc<AtomicTimestamp>,
) -> Box<dyn SequentialRunner> {
    if config.shard_count > 1 {
        build_sharded(config, tracker)
    } else {
        build_single(config, tracker, clock, shared_time)
    }
}

/// Build a single-shard sequential engine.
fn build_single(
    config: Arc<SimConfiguration>,
    tracker: EventTracker,
    clock: Clock,
    shared_time: Arc<AtomicTimestamp>,
) -> Box<dyn SequentialRunner> {
    let mut rng = ChaChaRng::seed_from_u64(config.seed);

    match config.variant {
        LeiosVariant::Linear | LeiosVariant::LinearWithTxReferences => {
            let (nodes, tx_rng) =
                init_node_impls::<LinearLeiosNode>(&config, &tracker, &clock, &mut rng);
            Box::new(build_single_sim(config, tracker, nodes, tx_rng, shared_time))
        }
        LeiosVariant::FullWithoutIbs => {
            let (nodes, tx_rng) =
                init_node_impls::<StracciatellaLeiosNode>(&config, &tracker, &clock, &mut rng);
            Box::new(build_single_sim(config, tracker, nodes, tx_rng, shared_time))
        }
        _ => {
            let (nodes, tx_rng) =
                init_node_impls::<LeiosNode>(&config, &tracker, &clock, &mut rng);
            Box::new(build_single_sim(config, tracker, nodes, tx_rng, shared_time))
        }
    }
}

fn build_single_sim<N: NodeImpl>(
    config: Arc<SimConfiguration>,
    tracker: EventTracker,
    node_impls: Vec<N>,
    tx_rng: ChaChaRng,
    shared_time: Arc<AtomicTimestamp>,
) -> SequentialSimulation<N> {
    let mut node_indices: HashMap<NodeId, usize> = HashMap::new();
    let mut nodes: Vec<NodeState<N>> = Vec::with_capacity(node_impls.len());

    for (idx, node) in node_impls.into_iter().enumerate() {
        let node_config = &config.nodes[idx];
        node_indices.insert(node_config.id, idx);
        nodes.push(NodeState {
            node,
            id: node_config.id,
            local_idx: idx,
            name: node_config.name.clone(),
            trace: config.trace_nodes.contains(&node_config.id),
            cpu: CpuTaskQueue::new(node_config.cores, node_config.cpu_multiplier),
            tracker: tracker.clone(),
            config: config.clone(),
        });
    }

    let mut connections: HashMap<Link, Connection<MiniProtocol, N::Message>> = HashMap::new();
    for link_config in &config.links {
        let (from, to) = link_config.nodes;
        connections.insert(
            Link { from, to },
            Connection::new(link_config.latency, link_config.bandwidth_bps),
        );
        connections.insert(
            Link { from: to, to: from },
            Connection::new(link_config.latency, link_config.bandwidth_bps),
        );
    }

    let tx_generator = TxGenerator::new(tx_rng, &config, &node_indices);

    let mut event_queue: BinaryHeap<FutureEvent<GlobalEvent<N>>> = BinaryHeap::new();
    for idx in 0..nodes.len() {
        event_queue.push(FutureEvent(
            Timestamp::zero(),
            GlobalEvent::NodeTimed {
                node_idx: idx,
                event: NodeEvent::NewSlot(0),
            },
        ));
    }
    if let Some(t) = tx_generator.first_event_time() {
        event_queue.push(FutureEvent(t, GlobalEvent::TxGeneration));
    }
    if config.slots != Some(0) {
        event_queue.push(FutureEvent(
            Timestamp::zero(),
            GlobalEvent::SlotBoundary { slot: 0 },
        ));
    }

    SequentialSimulation {
        nodes,
        node_indices,
        connections,
        event_queue,
        pending_deliveries: HashSet::new(),
        tx_generator,
        tracker,
        config,
        shared_time,
        is_primary: true,
        shard_index: 0,
        shard_lookup: None,
        cross_shard_tx: Vec::new(),
        cross_shard_rx: None,
        peer_shards: Vec::new(),
    }
}

/// Build a multi-shard sequential engine with CMB.
fn build_sharded(
    config: Arc<SimConfiguration>,
    tracker: EventTracker,
) -> Box<dyn SequentialRunner> {
    let mut rng = ChaChaRng::seed_from_u64(config.seed);

    match config.variant {
        LeiosVariant::Linear | LeiosVariant::LinearWithTxReferences => {
            build_sharded_typed::<LinearLeiosNode>(config, tracker, &mut rng)
        }
        LeiosVariant::FullWithoutIbs => {
            build_sharded_typed::<StracciatellaLeiosNode>(config, tracker, &mut rng)
        }
        _ => build_sharded_typed::<LeiosNode>(config, tracker, &mut rng),
    }
}

fn build_sharded_typed<N: NodeImpl + Send + 'static>(
    config: Arc<SimConfiguration>,
    tracker: EventTracker,
    rng: &mut ChaChaRng,
) -> Box<dyn SequentialRunner>
where
    N::Message: Send + Sync,
    N::Task: Send + Sync,
    N::TimedEvent: Send + Sync,
    N::CustomEvent: Send,
{
    let shard_count = config.shard_count;
    let shard_lookup: Arc<HashMap<NodeId, usize>> = crate::sharding::compute_shard_lookup(&config);

    // Create per-shard clock coordinators (for shared_time atomics only)
    let clock_coordinators: Vec<ClockCoordinator> = (0..shard_count)
        .map(|_| ClockCoordinator::new(config.timestamp_resolution))
        .collect();
    let shared_times: Vec<Arc<AtomicTimestamp>> = clock_coordinators
        .iter()
        .map(|cc| cc.shared_time())
        .collect();
    let clocks: Vec<Clock> = clock_coordinators.iter().map(|cc| cc.clock()).collect();

    // Create per-shard EventTrackers
    let trackers: Vec<EventTracker> = clocks
        .iter()
        .map(|clock| EventTracker::new(tracker.sender(), clock.clone(), &config.nodes))
        .collect();

    // Create node impls grouped by shard
    let mut per_shard_nodes: Vec<Vec<(usize, N)>> = (0..shard_count).map(|_| Vec::new()).collect();
    let mut per_shard_node_configs: Vec<Vec<usize>> = (0..shard_count).map(|_| Vec::new()).collect();

    for (global_idx, node_config) in config.nodes.iter().enumerate() {
        let shard = shard_lookup[&node_config.id];
        let node = N::new(
            node_config,
            config.clone(),
            trackers[shard].clone(),
            ChaChaRng::seed_from_u64(rng.next_u64()),
            clocks[shard].clone(),
        );
        per_shard_nodes[shard].push((global_idx, node));
        per_shard_node_configs[shard].push(global_idx);
    }

    // Create cross-shard channels: each shard gets all senders + its own receiver
    let (all_senders, receivers): (Vec<_>, Vec<_>) =
        (0..shard_count).map(|_| std_mpsc::channel()).unzip();
    let mut receivers: Vec<Option<std_mpsc::Receiver<CrossShardMsg<N::Message>>>> =
        receivers.into_iter().map(Some).collect();

    // Compute min cross-shard latencies for CMB
    let mut min_latencies = vec![vec![Duration::MAX; shard_count]; shard_count];
    for link in &config.links {
        let fs = shard_lookup[&link.nodes.0];
        let ts = shard_lookup[&link.nodes.1];
        if fs != ts {
            if link.latency < min_latencies[fs][ts] {
                min_latencies[fs][ts] = link.latency;
            }
            if link.latency < min_latencies[ts][fs] {
                min_latencies[ts][fs] = link.latency;
            }
        }
    }
    let min_lookahead = config.timestamp_resolution;

    // Build per-shard simulations
    let mut shards: Vec<SequentialSimulation<N>> = Vec::with_capacity(shard_count);

    for shard_idx in 0..shard_count {
        let shard_nodes_raw = std::mem::take(&mut per_shard_nodes[shard_idx]);

        // Build local node_indices (NodeId -> local index within this shard)
        let mut node_indices: HashMap<NodeId, usize> = HashMap::new();
        let mut nodes: Vec<NodeState<N>> = Vec::with_capacity(shard_nodes_raw.len());

        for (local_idx, (global_idx, node)) in shard_nodes_raw.into_iter().enumerate() {
            let node_config = &config.nodes[global_idx];
            node_indices.insert(node_config.id, local_idx);
            nodes.push(NodeState {
                node,
                id: node_config.id,
                local_idx,
                name: node_config.name.clone(),
                trace: config.trace_nodes.contains(&node_config.id),
                cpu: CpuTaskQueue::new(node_config.cores, node_config.cpu_multiplier),
                tracker: trackers[shard_idx].clone(),
                config: config.clone(),
            });
        }

        // Build connections: intra-shard + incoming cross-shard
        let mut connections: HashMap<Link, Connection<MiniProtocol, N::Message>> = HashMap::new();
        for link_config in &config.links {
            let (from, to) = link_config.nodes;
            let from_shard = shard_lookup[&from];
            let to_shard = shard_lookup[&to];

            if from_shard == shard_idx && to_shard == shard_idx {
                // Intra-shard: both directions
                connections.insert(
                    Link { from, to },
                    Connection::new(link_config.latency, link_config.bandwidth_bps),
                );
                connections.insert(
                    Link { from: to, to: from },
                    Connection::new(link_config.latency, link_config.bandwidth_bps),
                );
            } else if to_shard == shard_idx {
                // Incoming cross-shard edge: from→to, this shard owns the connection
                connections.insert(
                    Link { from, to },
                    Connection::new(link_config.latency, link_config.bandwidth_bps),
                );
            } else if from_shard == shard_idx {
                // Incoming cross-shard edge: to→from, this shard owns the connection
                connections.insert(
                    Link { from: to, to: from },
                    Connection::new(link_config.latency, link_config.bandwidth_bps),
                );
            }
        }

        // TX generator for this shard's nodes
        let tx_rng = ChaChaRng::seed_from_u64(rng.next_u64());
        let tx_generator = TxGenerator::new(tx_rng, &config, &node_indices);

        // Event queue with initial events
        let mut event_queue: BinaryHeap<FutureEvent<GlobalEvent<N>>> = BinaryHeap::new();
        for idx in 0..nodes.len() {
            event_queue.push(FutureEvent(
                Timestamp::zero(),
                GlobalEvent::NodeTimed {
                    node_idx: idx,
                    event: NodeEvent::NewSlot(0),
                },
            ));
        }
        if let Some(t) = tx_generator.first_event_time() {
            event_queue.push(FutureEvent(t, GlobalEvent::TxGeneration));
        }
        // Only shard 0 handles slot boundaries
        if shard_idx == 0 && config.slots != Some(0) {
            event_queue.push(FutureEvent(
                Timestamp::zero(),
                GlobalEvent::SlotBoundary { slot: 0 },
            ));
        }

        // CMB peer shard info
        let peer_shards: Vec<PeerShardInfo> = (0..shard_count)
            .filter(|&j| j != shard_idx)
            .filter(|&j| min_latencies[j][shard_idx] != Duration::MAX)
            .map(|j| PeerShardInfo {
                time: shared_times[j].clone(),
                min_latency: min_latencies[j][shard_idx].max(min_lookahead),
            })
            .collect();

        shards.push(SequentialSimulation {
            nodes,
            node_indices,
            connections,
            event_queue,
            pending_deliveries: HashSet::new(),
            tx_generator,
            tracker: trackers[shard_idx].clone(),
            config: config.clone(),
            shared_time: shared_times[shard_idx].clone(),
            is_primary: shard_idx == 0,
            shard_index: shard_idx,
            shard_lookup: Some(shard_lookup.clone()),
            cross_shard_tx: all_senders.clone(),
            cross_shard_rx: receivers[shard_idx].take(),
            peer_shards,
        });
    }

    Box::new(MultiShardRunner { shards })
}

/// Create node implementations without wrapping them in NodeDrivers.
fn init_node_impls<N: NodeImpl>(
    config: &Arc<SimConfiguration>,
    tracker: &EventTracker,
    clock: &Clock,
    rng: &mut ChaChaRng,
) -> (Vec<N>, ChaChaRng) {
    let mut node_impls = Vec::with_capacity(config.nodes.len());
    for node_config in &config.nodes {
        node_impls.push(N::new(
            node_config,
            config.clone(),
            tracker.clone(),
            ChaChaRng::seed_from_u64(rng.next_u64()),
            clock.clone(),
        ));
    }
    let tx_rng = ChaChaRng::seed_from_u64(rng.next_u64().wrapping_add(1));
    (node_impls, tx_rng)
}
