use std::{sync::Arc, time::Duration};

use anyhow::Result;
use rand_chacha::ChaChaRng;
use tokio::sync::mpsc;
use tokio_util::sync::CancellationToken;

use crate::{
    clock::{Clock, Timestamp},
    config::{CpuTimeConfig, NodeConfiguration, NodeId, SimConfiguration},
    events::EventTracker,
    model::Transaction,
};

pub(crate) mod actor;
mod common;
mod cpu;
mod driver;
mod leios;
mod linear_leios;
mod lottery;
pub(crate) mod sequential;
mod slot;
mod stracciatella;
#[cfg(test)]
mod tests;
pub(crate) mod tx;

// Re-export for the attacker module
pub(crate) use actor::{Actor, ActorInitArgs};

pub struct Simulation(SimulationInner);

enum SimulationInner {
    Actor(actor::ActorSimulation),
    Sequential(Box<dyn sequential::SequentialRunner>),
}

impl Simulation {
    pub async fn new(
        config: SimConfiguration,
        event_sender: mpsc::UnboundedSender<(crate::events::Event, Timestamp)>,
    ) -> Result<Self> {
        let config = Arc::new(config);

        match config.engine {
            crate::config::Engine::Sequential => {
                tracing::info!("using sequential DES engine");
                Ok(Self(SimulationInner::Sequential(sequential::build(
                    config,
                    event_sender,
                ))))
            }
            crate::config::Engine::Actor => {
                Ok(Self(SimulationInner::Actor(actor::ActorSimulation::new(
                    config,
                    event_sender,
                )?)))
            }
        }
    }

    pub async fn run(self, token: CancellationToken) -> Result<()> {
        match self.0 {
            SimulationInner::Sequential(seq) => {
                tokio::task::spawn_blocking(move || seq.run(token)).await?
            }
            SimulationInner::Actor(actor) => actor.run(token).await,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MiniProtocol {
    Tx,
    Block,
    IB,
    EB,
    Vote,
}

pub(crate) trait SimMessage: Clone + std::fmt::Debug {
    fn protocol(&self) -> MiniProtocol;
    fn bytes_size(&self) -> u64;
}

pub(crate) trait SimCpuTask {
    fn name(&self) -> String;
    fn extra(&self) -> String;
    fn times(&self, config: &CpuTimeConfig) -> Vec<Duration>;
}

pub(crate) struct EventResult<N: NodeImpl> {
    messages: Vec<(NodeId, N::Message)>,
    tasks: Vec<N::Task>,
    timed_events: Vec<(Timestamp, N::TimedEvent)>,
}

impl<N: NodeImpl> Default for EventResult<N> {
    fn default() -> Self {
        Self {
            messages: vec![],
            tasks: vec![],
            timed_events: vec![],
        }
    }
}

impl<N: NodeImpl> EventResult<N> {
    #[cfg(test)]
    pub fn merge(&mut self, mut other: EventResult<N>) {
        self.messages.append(&mut other.messages);
        self.tasks.append(&mut other.tasks);
        self.timed_events.append(&mut other.timed_events);
    }

    pub fn send_to(&mut self, to: NodeId, msg: N::Message) {
        self.messages.push((to, msg));
    }

    pub fn schedule_cpu_task(&mut self, task: N::Task) {
        self.tasks.push(task);
    }

    pub fn schedule_event(&mut self, time: Timestamp, event: N::TimedEvent) {
        self.timed_events.push((time, event));
    }
}

pub(crate) trait NodeImpl: Sized {
    type Message: SimMessage;
    type Task: SimCpuTask;
    type TimedEvent;
    type CustomEvent;

    fn new(
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        tracker: EventTracker,
        rng: ChaChaRng,
        clock: Clock,
    ) -> Self;

    fn custom_event_source(&mut self) -> Option<mpsc::UnboundedReceiver<Self::CustomEvent>> {
        None
    }

    fn handle_new_slot(&mut self, slot: u64) -> EventResult<Self>;
    fn handle_new_tx(&mut self, tx: Arc<Transaction>) -> EventResult<Self>;
    fn handle_message(&mut self, from: NodeId, msg: Self::Message) -> EventResult<Self>;
    fn handle_cpu_task(&mut self, task: Self::Task) -> EventResult<Self>;
    fn handle_timed_event(&mut self, event: Self::TimedEvent) -> EventResult<Self> {
        let _ = event;
        EventResult::default()
    }
    fn handle_custom_event(&mut self, event: Self::CustomEvent) -> EventResult<Self> {
        let _ = event;
        EventResult::default()
    }
}
