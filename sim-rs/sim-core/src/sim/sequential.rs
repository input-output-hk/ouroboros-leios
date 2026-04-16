use std::{
    collections::{BinaryHeap, HashMap, HashSet},
    sync::{Arc, atomic::Ordering, mpsc as std_mpsc},
    time::Duration,
};

use anyhow::Result;
use rand::RngCore;
use rand_chacha::{ChaChaRng, rand_core::SeedableRng};
use rayon::prelude::*;
use tokio_util::sync::CancellationToken;
use tracing::trace;

use crate::{
    clock::{Clock, ClockCoordinator, FutureEvent, Timestamp, timestamp::AtomicTimestamp},
    config::{LeiosVariant, NodeId, SimConfiguration},
    events::EventTracker,
    model::Transaction,
    network::connection::Connection,
    sim::{
        MiniProtocol, NodeImpl, SimMessage as _,
        common::{CpuTaskWrapper, NodeEvent, self},
        cpu::{CpuTaskQueue, Subtask},
        leios::LeiosNode,
        linear_leios::LinearLeiosNode,
        stracciatella::StracciatellaLeiosNode,
    },
};

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

use crate::sim::tx::TxGeneratorCore;

/// Cross-shard state for multi-shard CMB operation.
struct CrossShardState<M> {
    shard_index: usize,
    shard_lookup: Arc<HashMap<NodeId, usize>>,
    tx: Vec<std_mpsc::Sender<CrossShardMsg<M>>>,
    rx: std_mpsc::Receiver<CrossShardMsg<M>>,
    peer_shards: Vec<PeerShardInfo>,
}

/// The sequential discrete event simulation engine.
/// Supports both single-shard and multi-shard (CMB) operation.
pub(super) struct SequentialSimulation<N: NodeImpl> {
    nodes: Vec<NodeState<N>>,
    node_indices: HashMap<NodeId, usize>,
    connections: HashMap<Link, Connection<MiniProtocol, N::Message>>,
    event_queue: BinaryHeap<FutureEvent<GlobalEvent<N>>>,
    pending_deliveries: HashSet<Link>,
    tx_generator: TxGeneratorCore,
    tracker: EventTracker,
    config: Arc<SimConfiguration>,
    shared_time: Arc<AtomicTimestamp>,
    /// Whether this shard tracks global slot boundaries.
    is_primary: bool,
    /// Present only in multi-shard mode.
    cross_shard: Option<CrossShardState<N::Message>>,
}

impl<N: NodeImpl> SequentialSimulation<N> {
    /// Quantize a timestamp to the configured resolution.
    fn quantize(&self, t: Timestamp) -> Timestamp {
        t.with_resolution(self.config.timestamp_resolution)
    }

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

        // How long to sleep when blocked by CMB ceiling or waiting for messages.
        let blocked_timeout = Duration::from_micros(100);

        loop {
            if token.is_cancelled() {
                break;
            }

            // === Drain incoming cross-shard messages ===
            // Multi-shard is non-deterministic: try_recv/recv_timeout ordering
            // depends on OS scheduling of peer shard threads. Single-shard
            // (cross_shard is None) is deterministic after the bandwidth-queue
            // fix in Connection.
            if let Some(cs) = &self.cross_shard {
                let msgs: Vec<_> = std::iter::from_fn(|| cs.rx.try_recv().ok()).collect();
                for msg in msgs {
                    Self::deliver_cross_shard_msg(
                        &mut self.connections,
                        &mut self.pending_deliveries,
                        &mut self.event_queue,
                        msg,
                        self.config.timestamp_resolution,
                    );
                }
            }

            // === Check next event timestamp ===
            let Some(FutureEvent(timestamp, _)) = self.event_queue.peek() else {
                // No events — if we have peers, wait for cross-shard messages
                if let Some(cs) = &self.cross_shard {
                    if let Ok(msg) = cs.rx.recv_timeout(blocked_timeout) {
                        Self::deliver_cross_shard_msg(
                            &mut self.connections,
                            &mut self.pending_deliveries,
                            &mut self.event_queue,
                            msg,
                            self.config.timestamp_resolution,
                        );
                    }
                    continue;
                }
                break;
            };
            let timestamp = *timestamp;

            // === CMB ceiling check ===
            if let Some(cs) = &self.cross_shard {
                let ceiling = cs
                    .peer_shards
                    .iter()
                    .map(|p| p.time.load(Ordering::Acquire) + p.min_latency)
                    .min()
                    .unwrap_or(Timestamp::max());

                if timestamp > ceiling {
                    let current = self.shared_time.load(Ordering::Acquire);
                    if ceiling > current {
                        self.shared_time.store(ceiling, Ordering::Release);
                    }
                    if let Ok(msg) = cs.rx.recv_timeout(blocked_timeout) {
                        Self::deliver_cross_shard_msg(
                            &mut self.connections,
                            &mut self.pending_deliveries,
                            &mut self.event_queue,
                            msg,
                            self.config.timestamp_resolution,
                        );
                    }
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
                                self.quantize(next_arrival),
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
                        // When tx_batch_window is set, generate all TXs within
                        // that window in one batch. Otherwise generate one at a time.
                        let batch_end = self.config.tx_batch_window
                            .map(|w| timestamp + w);
                        while let Some((node_idx, tx, next_time)) =
                            self.tx_generator.generate(timestamp)
                        {
                            per_node_work[node_idx].push(WorkItem::NewTx(tx));
                            total_node_work += 1;
                            match next_time {
                                Some(t) if batch_end.is_some_and(|end| t <= end) => {
                                    // Next TX falls within the batch window — continue.
                                }
                                Some(t) => {
                                    self.event_queue
                                        .push(FutureEvent(self.quantize(t), GlobalEvent::TxGeneration));
                                    break;
                                }
                                None => break,
                            }
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
            if total_node_work >= self.config.parallel_threshold {
                let outputs: Vec<BatchNodeOutput<N>> = self
                    .nodes
                    .par_iter_mut()
                    .zip(per_node_work.par_iter_mut())
                    .filter(|(_, work)| !work.is_empty())
                    .map(|(node_state, work)| {
                        process_node_batch(node_state, std::mem::take(work), timestamp)
                    })
                    .collect();

                for output in outputs {
                    self.apply_batch_output(output, timestamp);
                }
            } else {
                for (node_idx, work) in per_node_work.iter_mut().enumerate().take(num_nodes) {
                    if work.is_empty() {
                        continue;
                    }
                    let work = std::mem::take(work);
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

    /// Deliver a single cross-shard message into the local connection.
    fn deliver_cross_shard_msg(
        connections: &mut HashMap<Link, Connection<MiniProtocol, N::Message>>,
        pending_deliveries: &mut HashSet<Link>,
        event_queue: &mut BinaryHeap<FutureEvent<GlobalEvent<N>>>,
        msg: CrossShardMsg<N::Message>,
        timestamp_resolution: Duration,
    ) {
        let link = Link {
            from: msg.from,
            to: msg.to,
        };
        if let Some(connection) = connections.get_mut(&link) {
            connection.send(msg.body, msg.bytes, msg.protocol, msg.send_time);
            if !pending_deliveries.contains(&link)
                && let Some(next_arrival) = connection.next_arrival_time()
            {
                pending_deliveries.insert(link.clone());
                event_queue.push(FutureEvent(
                    next_arrival.with_resolution(timestamp_resolution),
                    GlobalEvent::NetworkDelivery(link),
                ));
            }
        }
    }

    /// Apply the side effects from a batch of node processing.
    fn apply_batch_output(&mut self, output: BatchNodeOutput<N>, timestamp: Timestamp) {
        for (from_id, to, bytes, protocol, msg) in output.messages {
            // Check if this is a cross-shard message
            if let Some(cs) = &self.cross_shard {
                let target_shard = cs.shard_lookup[&to];
                if target_shard != cs.shard_index {
                    let _ = cs.tx[target_shard].send(CrossShardMsg {
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
                if !self.pending_deliveries.contains(&link)
                    && let Some(next_arrival) = connection.next_arrival_time()
                {
                    self.pending_deliveries.insert(link.clone());
                    self.event_queue.push(FutureEvent(
                        self.quantize(next_arrival),
                        GlobalEvent::NetworkDelivery(link),
                    ));
                }
            }
        }

        for mut event in output.new_events {
            event.0 = self.quantize(event.0);
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
                let result = common::complete_cpu_subtask::<N>(
                    &mut node_state.cpu, &node_state.tracker, node_state.id, timestamp, subtask,
                );
                if let Some(subtask) = result.next_subtask {
                    output.new_events.push(FutureEvent(
                        timestamp + subtask.duration,
                        GlobalEvent::NodeTimed {
                            node_idx,
                            event: NodeEvent::CpuSubtaskCompleted(subtask),
                        },
                    ));
                }
                let Some(task) = result.finished_task else {
                    continue;
                };
                node_state.node.handle_cpu_task(task)
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
            let subtasks = common::schedule_cpu_task::<N>(
                &mut node_state.cpu, &node_state.tracker, node_state.id, timestamp, task, &node_state.config,
            );
            for subtask in subtasks {
                output.new_events.push(FutureEvent(
                    timestamp + subtask.duration,
                    GlobalEvent::NodeTimed {
                        node_idx,
                        event: NodeEvent::CpuSubtaskCompleted(subtask),
                    },
                ));
            }
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
                    s.spawn(move || {
                        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            shard.run(token.clone())
                        }));
                        match result {
                            Ok(r) => r,
                            Err(payload) => {
                                token.cancel();
                                std::panic::resume_unwind(payload);
                            }
                        }
                    })
                })
                .collect();

            let mut first_error = None;
            for handle in handles {
                if let Err(e) = handle.join().unwrap()
                    && first_error.is_none()
                {
                    first_error = Some(e);
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
/// Handles both single-shard and multi-shard internally.
pub(super) fn build(
    config: Arc<SimConfiguration>,
    event_sender: tokio::sync::mpsc::UnboundedSender<(crate::events::Event, Timestamp)>,
) -> Box<dyn SequentialRunner> {
    if config.attacks.late_eb.is_some() {
        tracing::warn!(
            "sequential engine does not support attacker scenarios; late_eb_attack config will be ignored"
        );
    }

    let mut rng = ChaChaRng::seed_from_u64(config.seed);

    match config.variant {
        LeiosVariant::Linear | LeiosVariant::LinearWithTxReferences => {
            build_typed::<LinearLeiosNode>(config, event_sender, &mut rng)
        }
        LeiosVariant::FullWithoutIbs => {
            build_typed::<StracciatellaLeiosNode>(config, event_sender, &mut rng)
        }
        _ => build_typed::<LeiosNode>(config, event_sender, &mut rng),
    }
}

fn build_typed<N: NodeImpl + Send + 'static>(
    config: Arc<SimConfiguration>,
    event_sender: tokio::sync::mpsc::UnboundedSender<(crate::events::Event, Timestamp)>,
    rng: &mut ChaChaRng,
) -> Box<dyn SequentialRunner>
where
    N::Message: Send + Sync,
    N::Task: Send + Sync,
    N::TimedEvent: Send + Sync,
    N::CustomEvent: Send,
{
    let shard_count = config.shard_count;

    // Create per-shard clocks (for shared_time atomics and EventTracker)
    let clock_coordinators: Vec<ClockCoordinator> = (0..shard_count)
        .map(|_| ClockCoordinator::new(config.timestamp_resolution))
        .collect();
    let shared_times: Vec<Arc<AtomicTimestamp>> =
        clock_coordinators.iter().map(|cc| cc.shared_time()).collect();
    let clocks: Vec<Clock> = clock_coordinators.iter().map(|cc| cc.clock()).collect();
    let trackers: Vec<EventTracker> = clocks
        .iter()
        .map(|clock| EventTracker::new(event_sender.clone(), clock.clone(), &config.nodes))
        .collect();

    // Compute shard assignments
    let shard_lookup: Arc<HashMap<NodeId, usize>> =
        crate::sharding::compute_shard_lookup(&config);

    // Create node impls grouped by shard
    let mut per_shard_nodes: Vec<Vec<(usize, N)>> =
        (0..shard_count).map(|_| Vec::new()).collect();
    for (global_idx, node_config) in config.nodes.iter().enumerate() {
        let shard = shard_lookup[&node_config.id];
        per_shard_nodes[shard].push((
            global_idx,
            N::new(
                node_config,
                config.clone(),
                trackers[shard].clone(),
                ChaChaRng::seed_from_u64(rng.next_u64()),
                clocks[shard].clone(),
            ),
        ));
    }

    // Cross-shard wiring (only for multi-shard)
    let mut cross_shard_wiring = if shard_count > 1 {
        let (all_senders, receivers): (Vec<_>, Vec<_>) =
            (0..shard_count).map(|_| std_mpsc::channel()).unzip();
        let receivers: Vec<Option<std_mpsc::Receiver<CrossShardMsg<N::Message>>>> =
            receivers.into_iter().map(Some).collect();

        // Compute min cross-shard latencies for CMB
        let min_lookahead = config.timestamp_resolution;
        let mut min_latencies = vec![vec![Duration::MAX; shard_count]; shard_count];
        for link in &config.links {
            let fs = shard_lookup[&link.nodes.0];
            let ts = shard_lookup[&link.nodes.1];
            if fs != ts {
                min_latencies[fs][ts] = min_latencies[fs][ts].min(link.latency);
                min_latencies[ts][fs] = min_latencies[ts][fs].min(link.latency);
            }
        }

        Some((all_senders, receivers, min_latencies, min_lookahead))
    } else {
        None
    };

    // Build per-shard simulations
    let mut shards: Vec<SequentialSimulation<N>> = Vec::with_capacity(shard_count);

    for shard_idx in 0..shard_count {
        let shard_nodes = std::mem::take(&mut per_shard_nodes[shard_idx]);

        // Build nodes with local indices
        let mut node_indices: HashMap<NodeId, usize> = HashMap::new();
        let mut nodes: Vec<NodeState<N>> = Vec::with_capacity(shard_nodes.len());
        for (local_idx, (global_idx, node)) in shard_nodes.into_iter().enumerate() {
            let nc = &config.nodes[global_idx];
            node_indices.insert(nc.id, local_idx);
            nodes.push(NodeState {
                node,
                id: nc.id,
                local_idx,
                name: nc.name.clone(),
                trace: config.trace_nodes.contains(&nc.id),
                cpu: CpuTaskQueue::new(nc.cores, nc.cpu_multiplier),
                tracker: trackers[shard_idx].clone(),
                config: config.clone(),
            });
        }

        // Build connections
        let mut connections: HashMap<Link, Connection<MiniProtocol, N::Message>> = HashMap::new();
        for lc in &config.links {
            let (from, to) = lc.nodes;
            let fs = shard_lookup[&from];
            let ts = shard_lookup[&to];
            if shard_count == 1 || (fs == shard_idx && ts == shard_idx) {
                // Intra-shard (or single-shard): both directions
                connections.insert(
                    Link { from, to },
                    Connection::new(lc.latency, lc.bandwidth_bps),
                );
                connections.insert(
                    Link { from: to, to: from },
                    Connection::new(lc.latency, lc.bandwidth_bps),
                );
            } else if ts == shard_idx {
                connections.insert(
                    Link { from, to },
                    Connection::new(lc.latency, lc.bandwidth_bps),
                );
            } else if fs == shard_idx {
                connections.insert(
                    Link { from: to, to: from },
                    Connection::new(lc.latency, lc.bandwidth_bps),
                );
            }
        }

        // TX generator + initial events
        let tx_rng = ChaChaRng::seed_from_u64(rng.next_u64());
        let indexed_nodes: Vec<_> = config.nodes.iter()
            .filter_map(|n| node_indices.get(&n.id).map(|&idx| (idx, n)))
            .collect();
        let tx_generator = TxGeneratorCore::new(tx_rng, &config, indexed_nodes);
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
        let is_primary = shard_idx == 0;
        if is_primary && config.slots != Some(0) {
            event_queue.push(FutureEvent(
                Timestamp::zero(),
                GlobalEvent::SlotBoundary { slot: 0 },
            ));
        }

        // Cross-shard state
        let cross_shard = if let Some((ref senders, ref mut receivers, ref min_latencies, min_lookahead)) =
            cross_shard_wiring
        {
            let peer_shards: Vec<PeerShardInfo> = (0..shard_count)
                .filter(|&j| j != shard_idx && min_latencies[j][shard_idx] != Duration::MAX)
                .map(|j| PeerShardInfo {
                    time: shared_times[j].clone(),
                    min_latency: min_latencies[j][shard_idx].max(min_lookahead),
                })
                .collect();
            Some(CrossShardState {
                shard_index: shard_idx,
                shard_lookup: shard_lookup.clone(),
                tx: senders.clone(),
                rx: receivers[shard_idx].take().unwrap(),
                peer_shards,
            })
        } else {
            None
        };

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
            is_primary,
            cross_shard,
        });
    }

    if shards.len() == 1 {
        Box::new(shards.pop().unwrap())
    } else {
        Box::new(MultiShardRunner { shards })
    }
}

#[cfg(test)]
pub(crate) fn build_for_test<N: NodeImpl + Send + 'static>(
    config: Arc<SimConfiguration>,
    event_sender: tokio::sync::mpsc::UnboundedSender<(crate::events::Event, Timestamp)>,
    rng: &mut ChaChaRng,
) -> Box<dyn SequentialRunner>
where
    N::Message: Send + Sync,
    N::Task: Send + Sync,
    N::TimedEvent: Send + Sync,
    N::CustomEvent: Send,
{
    build_typed::<N>(config, event_sender, rng)
}
