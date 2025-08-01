use std::{cmp::Reverse, sync::Arc, time::Duration};

use futures::{FutureExt, future::BoxFuture};
use priority_queue::PriorityQueue;
use tokio::{select, sync::mpsc};

use super::LinearLeiosNode;
use crate::{
    clock::{ClockBarrier, TaskInitiator, Timestamp},
    config::NodeId,
    events::EventTracker,
    model::{EndorserBlockId, LinearEndorserBlock as EndorserBlock},
    sim::{Actor, ActorInitArgs},
};

#[derive(Clone)]
pub struct EBWithholdingSender {
    sender: mpsc::UnboundedSender<Arc<EndorserBlock>>,
    tasks: TaskInitiator,
}
impl EBWithholdingSender {
    pub fn send(&self, message: Arc<EndorserBlock>) {
        self.tasks.start_task();
        let _ = self.sender.send(message);
    }
}

pub enum EBWithholdingEvent {
    NewEB(Arc<EndorserBlock>),
    DisseminateEB(EndorserBlockId),
}

struct EBWithholdingAttacker {
    tracker: EventTracker,
    clock: ClockBarrier,
    propagation_delay: Duration,
    receiver: mpsc::UnboundedReceiver<Arc<EndorserBlock>>,
    channels: Vec<(NodeId, mpsc::UnboundedSender<EBWithholdingEvent>)>,
    announcements: PriorityQueue<EndorserBlockId, Reverse<Timestamp>>,
}

impl Actor for EBWithholdingAttacker {
    fn run(self: Box<Self>) -> BoxFuture<'static, anyhow::Result<()>> {
        self.do_run().boxed()
    }
}

impl EBWithholdingAttacker {
    fn new(
        tracker: EventTracker,
        clock: ClockBarrier,
        propagation_delay: Duration,
        receiver: mpsc::UnboundedReceiver<Arc<EndorserBlock>>,
        channels: Vec<(NodeId, mpsc::UnboundedSender<EBWithholdingEvent>)>,
    ) -> Self {
        Self {
            tracker,
            clock,
            propagation_delay,
            receiver,
            channels,
            announcements: PriorityQueue::new(),
        }
    }

    async fn do_run(mut self) -> anyhow::Result<()> {
        loop {
            let waiter = match self.announcements.peek() {
                Some((_, Reverse(timestamp))) => self.clock.wait_until(*timestamp),
                None => self.clock.wait_forever(),
            };
            select! {
                () = waiter => {
                    let Some((eb_id, Reverse(timestamp))) = self.announcements.pop() else {
                        return Ok(());
                    };
                    assert!(self.clock.now() >= timestamp);
                    for (_, channel) in &mut self.channels {
                        let _ = channel.send(EBWithholdingEvent::DisseminateEB(eb_id));
                        self.clock.start_task();
                    }
                },
                Some(eb) = self.receiver.recv() => {
                    self.share_eb(eb);
                    self.clock.finish_task();
                }
            }
        }
    }

    fn share_eb(&mut self, eb: Arc<EndorserBlock>) {
        // Send this EB to all of the attacker nodes.
        // They should vote on it immediately, to get as many votes as possible
        // without sharing it with the victims.
        for (node_id, channel) in &self.channels {
            if *node_id == eb.producer {
                // The producer already has it!
                continue;
            }

            // We're assuming that the EBs are getting sent through a side channel.
            // To avoid breaking scripts which analyze trace output,
            // we emit EBSent and EBReceived events,
            // as if the original node had instantly transmitted the EB to all peers.
            self.tracker
                .track_linear_eb_sent(&eb, eb.producer, *node_id);
            self.tracker
                .track_eb_received(eb.id(), eb.producer, *node_id);

            let _ = channel.send(EBWithholdingEvent::NewEB(eb.clone()));
            self.clock.start_task();
        }

        // These nefarious nodes will announce the EB to the rest of the world after some delay.
        self.announcements
            .push(eb.id(), Reverse(self.clock.now() + self.propagation_delay));
    }
}

pub fn register_actors(args: ActorInitArgs<LinearLeiosNode>) -> Vec<Box<dyn Actor>> {
    let Some(late_eb_config) = args.config.attacks.late_eb.as_ref() else {
        return vec![];
    };

    let clock = args.clock.barrier();
    let (eb_sender, eb_receiver) = mpsc::unbounded_channel();
    let sender = EBWithholdingSender {
        sender: eb_sender,
        tasks: clock.task_initiator(),
    };
    let mut attacker_channels = vec![];
    for node in args.nodes {
        if late_eb_config.attackers.contains(&node.id) {
            let channel = node.register_as_eb_withholder(sender.clone());
            attacker_channels.push((node.id, channel));
        }
    }
    let actor = EBWithholdingAttacker::new(
        args.tracker.clone(),
        clock,
        late_eb_config.propagation_delay,
        eb_receiver,
        attacker_channels,
    );
    vec![Box::new(actor)]
}
