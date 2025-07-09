use std::{collections::BinaryHeap, sync::Arc, time::Duration};

use netsim_async::HasBytesSize as _;
use tokio::{select, sync::mpsc};
use tracing::trace;

use crate::{
    clock::{ClockBarrier, FutureEvent, Timestamp},
    config::{NodeConfiguration, NodeId, SimConfiguration},
    events::EventTracker,
    model::{CpuTaskId, Transaction},
    network::{Network, NetworkSink, NetworkSource},
    sim::{
        CpuTask, EventResult, MiniProtocol, NodeImpl, SimulationMessage,
        cpu::{CpuTaskQueue, Subtask},
    },
};

struct CpuTaskWrapper<Task: CpuTask> {
    task_type: Task,
    start_time: Timestamp,
    cpu_time: Duration,
}

enum NodeEvent {
    NewSlot(u64),
    CpuSubtaskCompleted(Subtask),
}

pub struct NodeDriver<N: NodeImpl> {
    node: N,
    id: NodeId,
    name: String,
    trace: bool,
    sim_config: Arc<SimConfiguration>,
    msg_source: NetworkSource<SimulationMessage>,
    msg_sink: NetworkSink<MiniProtocol, SimulationMessage>,
    tx_source: mpsc::UnboundedReceiver<Arc<Transaction>>,
    events: BinaryHeap<FutureEvent<NodeEvent>>,
    tracker: EventTracker,
    clock: ClockBarrier,
    cpu: CpuTaskQueue<CpuTaskWrapper<N::Task>>,
}

impl<N: NodeImpl> NodeDriver<N> {
    pub fn new(
        node: N,
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        network: &mut Network<MiniProtocol, SimulationMessage>,
        tx_source: mpsc::UnboundedReceiver<Arc<Transaction>>,
        tracker: EventTracker,
        clock: ClockBarrier,
    ) -> Self {
        let (msg_sink, msg_source) = network.open(config.id).unwrap();
        let mut events = BinaryHeap::new();
        events.push(FutureEvent(clock.now(), NodeEvent::NewSlot(0)));

        Self {
            node,
            id: config.id,
            name: config.name.clone(),
            trace: sim_config.trace_nodes.contains(&config.id),
            sim_config,
            msg_source,
            msg_sink,
            tx_source,
            events,
            tracker,
            clock,
            cpu: CpuTaskQueue::new(config.cores, config.cpu_multiplier),
        }
    }

    pub async fn run(mut self) -> anyhow::Result<()> {
        loop {
            let next_event_at = self.events.peek().map(|e| e.0).expect("no events");
            let (result, finish_task) = select! {
                maybe_msg = self.msg_source.recv() => {
                    let Some((from, msg)) = maybe_msg else {
                        // sim has stopped running
                        return Ok(());
                    };
                    (self.node.handle_message(from, msg), true)
                }
                maybe_tx = self.tx_source.recv() => {
                    let Some(tx) = maybe_tx else {
                        // sim has stopped running
                        return Ok(());
                    };
                    (self.node.handle_new_tx(tx), false)
                }
                () = self.clock.wait_until(next_event_at) => {
                    let event = self.events.pop().unwrap().1;
                    match event {
                        NodeEvent::NewSlot(slot) => {
                            if self.sim_config.emit_conformance_events && slot > 0 {
                                self.tracker.track_slot(self.id, slot - 1);
                            }
                            self.events.push(FutureEvent(self.clock.now() + Duration::from_secs(1), NodeEvent::NewSlot(slot + 1)));
                            (self.node.handle_new_slot(slot), false)
                        }
                        NodeEvent::CpuSubtaskCompleted(subtask) => {
                            let Some(result) = self.handle_subtask_completed(subtask) else {
                                continue;
                            };
                            (result, false)
                        }
                    }
                }
            };
            for (to, msg) in result.messages {
                self.send_to(to, msg)?;
            }
            for task in result.tasks {
                self.schedule_cpu_task(task);
            }
            if finish_task {
                self.clock.finish_task();
            }
        }
    }

    fn send_to(&self, to: NodeId, msg: SimulationMessage) -> anyhow::Result<()> {
        if self.trace {
            trace!(
                "node {} sent msg of size {} to node {to}",
                self.name,
                msg.bytes_size()
            );
        }
        self.clock.start_task();
        self.msg_sink
            .send_to(to, msg.bytes_size(), msg.protocol(), msg)
    }

    fn schedule_cpu_task(&mut self, task: N::Task) {
        let cpu_times = task.times(&self.sim_config.cpu_times);
        let task = CpuTaskWrapper {
            task_type: task,
            start_time: self.clock.now(),
            cpu_time: cpu_times.iter().sum(),
        };
        let name = task.task_type.name();
        let subtask_count = cpu_times.len();
        let (task_id, subtasks) = self.cpu.schedule_task(task, cpu_times);
        self.tracker.track_cpu_task_scheduled(
            CpuTaskId {
                node: self.id,
                index: task_id,
            },
            name.clone(),
            subtask_count,
        );
        for subtask in subtasks {
            self.start_cpu_subtask(subtask, name.clone());
        }
    }

    fn handle_subtask_completed(&mut self, subtask: Subtask) -> Option<EventResult<N::Task>> {
        let task_id = CpuTaskId {
            node: self.id,
            index: subtask.task_id,
        };
        let (finished_task, next_subtask) = self.cpu.complete_subtask(subtask);
        if let Some((subtask, task)) = next_subtask {
            let task_type = task.task_type.name();
            self.start_cpu_subtask(subtask, task_type);
        }
        let task = finished_task?;
        let wall_time = self.clock.now() - task.start_time;
        self.tracker.track_cpu_task_finished(
            task_id,
            task.task_type.name(),
            task.cpu_time,
            wall_time,
            task.task_type.extra(),
        );
        Some(self.node.handle_cpu_task(task.task_type))
    }

    fn start_cpu_subtask(&mut self, subtask: Subtask, task_type: String) {
        let task_id = CpuTaskId {
            node: self.id,
            index: subtask.task_id,
        };
        self.tracker.track_cpu_subtask_started(
            task_id,
            task_type,
            subtask.subtask_id,
            subtask.duration,
        );
        let timestamp = self.clock.now() + subtask.duration;
        self.events.push(FutureEvent(
            timestamp,
            NodeEvent::CpuSubtaskCompleted(subtask),
        ))
    }
}
