use std::{collections::BinaryHeap, sync::Arc, time::Duration};

use futures::future::OptionFuture;
use tokio::{select, sync::mpsc};
use tracing::trace;

use crate::{
    clock::{ClockBarrier, FutureEvent},
    config::{NodeConfiguration, NodeId, SimConfiguration},
    events::EventTracker,
    model::Transaction,
    network::{Network, NetworkSink, NetworkSource},
    sim::{
        EventResult, MiniProtocol, NodeImpl, SimMessage as _,
        common::{CpuTaskWrapper, NodeEvent, self},
        cpu::CpuTaskQueue,
    },
};

pub struct NodeDriver<N: NodeImpl> {
    node: N,
    id: NodeId,
    name: String,
    trace: bool,
    sim_config: Arc<SimConfiguration>,
    msg_source: NetworkSource<N::Message>,
    msg_sink: NetworkSink<MiniProtocol, N::Message>,
    tx_source: mpsc::UnboundedReceiver<Arc<Transaction>>,
    events: BinaryHeap<FutureEvent<NodeEvent<N::TimedEvent>>>,
    tracker: EventTracker,
    clock: ClockBarrier,
    cpu: CpuTaskQueue<CpuTaskWrapper<N::Task>>,
}

impl<N: NodeImpl> NodeDriver<N> {
    pub fn new(
        node: N,
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        network: &mut Network<MiniProtocol, N::Message>,
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
        let mut custom_event_source = self.node.custom_event_source();
        let has_custom_event_source = custom_event_source.is_some();
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
                maybe_custom_event = OptionFuture::from(custom_event_source.as_mut().map(|s| s.recv())), if has_custom_event_source => {
                    let Some(Some(event)) = maybe_custom_event else {
                        // sim has stopped running
                        return Ok(());
                    };
                    (self.node.handle_custom_event(event), true)
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
                        NodeEvent::Other(event) => {
                            (self.node.handle_timed_event(event), false)
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
            for (time, event) in result.timed_events {
                self.events.push(FutureEvent(time, NodeEvent::Other(event)));
            }
            if finish_task {
                self.clock.finish_task();
            }
        }
    }

    fn send_to(&self, to: NodeId, msg: N::Message) -> anyhow::Result<()> {
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
        let now = self.clock.now();
        let subtasks =
            common::schedule_cpu_task::<N>(&mut self.cpu, &self.tracker, self.id, now, task, &self.sim_config);
        for subtask in subtasks {
            let timestamp = now + subtask.duration;
            self.events
                .push(FutureEvent(timestamp, NodeEvent::CpuSubtaskCompleted(subtask)));
        }
    }

    fn handle_subtask_completed(&mut self, subtask: crate::sim::cpu::Subtask) -> Option<EventResult<N>> {
        let now = self.clock.now();
        let result =
            common::complete_cpu_subtask::<N>(&mut self.cpu, &self.tracker, self.id, now, subtask);
        if let Some(subtask) = result.next_subtask {
            let timestamp = now + subtask.duration;
            self.events
                .push(FutureEvent(timestamp, NodeEvent::CpuSubtaskCompleted(subtask)));
        }
        let task = result.finished_task?;
        Some(self.node.handle_cpu_task(task))
    }
}
