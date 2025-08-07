use std::{collections::BinaryHeap, sync::Arc, time::Duration};

use futures::{FutureExt, future::BoxFuture};
use tokio::{select, sync::mpsc};

use super::LinearLeiosNode;
use crate::{
    clock::{ClockBarrier, FutureEvent, TaskInitiator},
    config::NodeId,
    events::EventTracker,
    model::{EndorserBlockId, LinearEndorserBlock as EndorserBlock, Transaction, TransactionId},
    sim::{Actor, ActorInitArgs},
};

#[derive(Clone)]
pub struct EBWithholdingSender {
    sender: mpsc::UnboundedSender<(Arc<EndorserBlock>, Vec<Arc<Transaction>>)>,
    tasks: TaskInitiator,
}
impl EBWithholdingSender {
    pub fn send(&self, eb: Arc<EndorserBlock>, withheld_txs: Vec<Arc<Transaction>>) {
        self.tasks.start_task();
        let _ = self.sender.send((eb, withheld_txs));
    }
}

pub enum EBWithholdingEvent {
    NewEB(Arc<EndorserBlock>, Vec<Arc<Transaction>>),
    DisseminateEB(EndorserBlockId, Vec<TransactionId>),
}

struct DisseminateEBAnnouncement {
    eb_id: EndorserBlockId,
    withheld_txs: Vec<TransactionId>,
}

struct EBWithholdingAttacker {
    tracker: EventTracker,
    clock: ClockBarrier,
    propagation_delay: Duration,
    receiver: mpsc::UnboundedReceiver<(Arc<EndorserBlock>, Vec<Arc<Transaction>>)>,
    channels: Vec<(NodeId, mpsc::UnboundedSender<EBWithholdingEvent>)>,
    announcements: BinaryHeap<FutureEvent<DisseminateEBAnnouncement>>,
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
        receiver: mpsc::UnboundedReceiver<(Arc<EndorserBlock>, Vec<Arc<Transaction>>)>,
        channels: Vec<(NodeId, mpsc::UnboundedSender<EBWithholdingEvent>)>,
    ) -> Self {
        Self {
            tracker,
            clock,
            propagation_delay,
            receiver,
            channels,
            announcements: BinaryHeap::new(),
        }
    }

    async fn do_run(mut self) -> anyhow::Result<()> {
        loop {
            let waiter = match self.announcements.peek() {
                Some(FutureEvent(timestamp, _)) => self.clock.wait_until(*timestamp),
                None => self.clock.wait_forever(),
            };
            select! {
                () = waiter => {
                    let Some(FutureEvent(timestamp, announcement)) = self.announcements.pop() else {
                        return Ok(());
                    };
                    assert!(self.clock.now() >= timestamp);
                    for (_, channel) in &mut self.channels {
                        let _ = channel.send(EBWithholdingEvent::DisseminateEB(announcement.eb_id, announcement.withheld_txs.clone()));
                        self.clock.start_task();
                    }
                },
                Some((eb, withheld_txs)) = self.receiver.recv() => {
                    self.share_eb(eb, withheld_txs);
                    self.clock.finish_task();
                }
            }
        }
    }

    fn share_eb(&mut self, eb: Arc<EndorserBlock>, withheld_txs: Vec<Arc<Transaction>>) {
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

            // Same with any withheld TXs which are coming along for the ride
            for tx in &withheld_txs {
                self.tracker
                    .track_transaction_sent(tx, eb.producer, *node_id);
                self.tracker
                    .track_transaction_received(tx.id, eb.producer, *node_id);
            }

            let _ = channel.send(EBWithholdingEvent::NewEB(eb.clone(), withheld_txs.clone()));
            self.clock.start_task();
        }

        // These nefarious nodes will announce the EB to the rest of the world after some delay.
        let announcement = DisseminateEBAnnouncement {
            eb_id: eb.id(),
            withheld_txs: withheld_txs.into_iter().map(|tx| tx.id).collect(),
        };
        self.announcements.push(FutureEvent(
            self.clock.now() + self.propagation_delay,
            announcement,
        ));
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
