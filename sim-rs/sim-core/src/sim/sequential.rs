use std::{
    collections::{BinaryHeap, HashMap, HashSet},
    sync::{Arc, atomic::Ordering},
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
    clock::{Clock, FutureEvent, Timestamp, timestamp::AtomicTimestamp},
    config::{NodeId, RealTransactionConfig, SimConfiguration, TransactionConfig},
    events::EventTracker,
    model::{CpuTaskId, Transaction},
    network::connection::Connection,
    sim::{
        MiniProtocol, NodeImpl, SimCpuTask, SimMessage as _,
        cpu::{CpuTaskQueue, Subtask},
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
    /// A node-local timed event.
    NodeTimed {
        node_idx: usize,
        event: NodeEvent<N::TimedEvent>,
    },
    /// A network connection has messages ready for delivery.
    NetworkDelivery(Link),
    /// Transaction generation tick.
    TxGeneration,
    /// Simulation slot boundary (for EventTracker global slot tracking).
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
    /// Outgoing messages: (from_id, to_id, bytes, protocol, msg)
    messages: Vec<(NodeId, NodeId, u64, MiniProtocol, N::Message)>,
    /// New events to push to the global queue
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

/// Minimum batch size to use rayon parallelism. Below this, process sequentially.
const PARALLEL_THRESHOLD: usize = 32;

/// Transaction generation state (replaces TransactionProducer actor).
struct TxGenerator {
    rng: ChaChaRng,
    config: Option<RealTransactionConfig>,
    node_weights: Vec<(usize, u64)>, // (node_idx, cumulative_weight)
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
        let mut tx_conflict_fractions = vec![None; config.nodes.len()];

        for node_config in &config.nodes {
            let Some(&idx) = node_indices.get(&node_config.id) else {
                continue;
            };
            tx_conflict_fractions[idx] = node_config.tx_conflict_fraction;
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

    /// Generate one transaction. Returns (target_node_idx, tx, next_gen_time).
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

        let tx = config.new_tx(&mut self.rng, self.tx_conflict_fractions[idx]);

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
pub(super) struct SequentialSimulation<N: NodeImpl> {
    nodes: Vec<NodeState<N>>,
    node_indices: HashMap<NodeId, usize>,
    connections: HashMap<Link, Connection<MiniProtocol, N::Message>>,
    event_queue: BinaryHeap<FutureEvent<GlobalEvent<N>>>,
    /// Track which links already have a NetworkDelivery event in the queue.
    pending_deliveries: HashSet<Link>,
    tx_generator: TxGenerator,
    tracker: EventTracker,
    config: Arc<SimConfiguration>,
    /// Shared atomic timestamp — updated as time advances.
    shared_time: Arc<AtomicTimestamp>,
}

impl<N: NodeImpl> SequentialSimulation<N> {
    pub(super) fn new(
        config: Arc<SimConfiguration>,
        tracker: EventTracker,
        node_impls: Vec<N>,
        tx_rng: ChaChaRng,
        shared_time: Arc<AtomicTimestamp>,
    ) -> Self {
        let mut node_indices: HashMap<NodeId, usize> = HashMap::new();
        let mut nodes: Vec<NodeState<N>> = Vec::with_capacity(node_impls.len());

        for (idx, node) in node_impls.into_iter().enumerate() {
            let node_config = &config.nodes[idx];
            node_indices.insert(node_config.id, idx);
            nodes.push(NodeState {
                node,
                id: node_config.id,
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

        // Schedule initial NewSlot(0) for all nodes
        for idx in 0..nodes.len() {
            event_queue.push(FutureEvent(
                Timestamp::zero(),
                GlobalEvent::NodeTimed {
                    node_idx: idx,
                    event: NodeEvent::NewSlot(0),
                },
            ));
        }

        // Schedule first TX generation
        if let Some(t) = tx_generator.first_event_time() {
            event_queue.push(FutureEvent(t, GlobalEvent::TxGeneration));
        }

        // Schedule first slot boundary
        if config.slots != Some(0) {
            event_queue.push(FutureEvent(
                Timestamp::zero(),
                GlobalEvent::SlotBoundary { slot: 0 },
            ));
        }

        Self {
            nodes,
            node_indices,
            connections,
            event_queue,
            pending_deliveries: HashSet::new(),
            tx_generator,
            tracker,
            config,
            shared_time,
        }
    }

    /// Run the simulation using BSP batch processing with rayon parallelism.
    pub(super) fn run(mut self, token: CancellationToken) -> Result<()>
    where
        N: Send,
        N::Message: Send,
        N::Task: Send,
        N::TimedEvent: Send,
    {
        // Per-node work buffers, reused across batches
        let num_nodes = self.nodes.len();
        let mut per_node_work: Vec<Vec<WorkItem<N>>> = (0..num_nodes).map(|_| Vec::new()).collect();

        while let Some(FutureEvent(timestamp, _)) = self.event_queue.peek() {
            if token.is_cancelled() {
                break;
            }

            let timestamp = *timestamp;
            self.shared_time.store(timestamp, Ordering::Release);

            // === Phase 1: Pop all events at this timestamp ===
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
                        // Resolve delivery: extract messages from connection (sequential)
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
                        // TX generation is sequential (uses RNG)
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
                        self.tracker.track_global_slot(slot);
                        let next_slot = slot + 1;
                        if self.config.slots == Some(next_slot) {
                            done = true;
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

            // === Phase 2: Compute — process node work items ===
            if total_node_work >= PARALLEL_THRESHOLD {
                // Parallel path: use rayon
                let outputs: Vec<BatchNodeOutput<N>> = self
                    .nodes
                    .par_iter_mut()
                    .zip(per_node_work.par_iter_mut())
                    .filter(|(_, work)| !work.is_empty())
                    .map(|(node_state, work)| {
                        process_node_batch(node_state, work.drain(..).collect(), timestamp)
                    })
                    .collect();

                // === Phase 3: Apply results sequentially ===
                for output in outputs {
                    self.apply_batch_output(output, timestamp);
                }
            } else {
                // Sequential path: avoid rayon overhead for small batches
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

            // Clear work buffers (drain should have emptied them, but be safe)
            for work in &mut per_node_work {
                work.clear();
            }
        }

        Ok(())
    }

    /// Apply the side effects from a batch of node processing.
    fn apply_batch_output(&mut self, output: BatchNodeOutput<N>, timestamp: Timestamp) {
        // Send messages through connections
        for (from_id, to, bytes, protocol, msg) in output.messages {
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

        // Push new events to the global queue
        for event in output.new_events {
            self.event_queue.push(event);
        }
    }
}

/// Process a batch of work items for a single node. Called from parallel context.
/// Only accesses the node's own state — no shared mutable state.
fn process_node_batch<N: NodeImpl>(
    node_state: &mut NodeState<N>,
    work: Vec<WorkItem<N>>,
    timestamp: Timestamp,
) -> BatchNodeOutput<N> {
    let mut output = BatchNodeOutput::default();
    let node_idx = node_state.id.to_inner();
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

        // Collect messages with metadata for the apply phase
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

        // Schedule CPU tasks
        for task in result.tasks {
            schedule_cpu_task_batch(node_state, &mut output, node_idx, timestamp, task);
        }

        // Schedule timed events
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

/// Build a sequential DES engine for the given config + variant.
/// Handles node creation and variant dispatch internally.
pub(super) fn build(
    config: Arc<SimConfiguration>,
    tracker: EventTracker,
    clock: Clock,
    shared_time: Arc<AtomicTimestamp>,
) -> Box<dyn SequentialRunner> {
    use super::{
        leios::LeiosNode, linear_leios::LinearLeiosNode,
        stracciatella::StracciatellaLeiosNode,
    };
    use crate::config::LeiosVariant;

    let mut rng = ChaChaRng::seed_from_u64(config.seed);

    match config.variant {
        LeiosVariant::Linear | LeiosVariant::LinearWithTxReferences => {
            let (nodes, tx_rng) =
                init_node_impls::<LinearLeiosNode>(&config, &tracker, &clock, &mut rng);
            Box::new(SequentialSimulation::new(
                config, tracker, nodes, tx_rng, shared_time,
            ))
        }
        LeiosVariant::FullWithoutIbs => {
            let (nodes, tx_rng) =
                init_node_impls::<StracciatellaLeiosNode>(&config, &tracker, &clock, &mut rng);
            Box::new(SequentialSimulation::new(
                config, tracker, nodes, tx_rng, shared_time,
            ))
        }
        _ => {
            let (nodes, tx_rng) =
                init_node_impls::<LeiosNode>(&config, &tracker, &clock, &mut rng);
            Box::new(SequentialSimulation::new(
                config, tracker, nodes, tx_rng, shared_time,
            ))
        }
    }
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
