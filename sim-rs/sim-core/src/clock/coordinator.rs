use std::{
    collections::BTreeMap,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use tokio::sync::{mpsc, oneshot};

use super::{timestamp::AtomicTimestamp, Clock, Timestamp};

pub struct ClockCoordinator {
    time: Arc<AtomicTimestamp>,
    tx: mpsc::UnboundedSender<ClockEvent>,
    rx: mpsc::UnboundedReceiver<ClockEvent>,
    waiter_count: Arc<AtomicUsize>,
}

impl Default for ClockCoordinator {
    fn default() -> Self {
        Self::new()
    }
}

impl ClockCoordinator {
    pub fn new() -> Self {
        let time = Arc::new(AtomicTimestamp::new(Timestamp::zero()));
        let (tx, rx) = mpsc::unbounded_channel();
        let waiter_count = Arc::new(AtomicUsize::new(0));
        Self {
            time,
            tx,
            rx,
            waiter_count,
        }
    }

    pub fn clock(&self) -> Clock {
        Clock::new(
            self.time.clone(),
            self.waiter_count.clone(),
            self.tx.clone(),
        )
    }

    pub async fn run(&mut self) {
        let mut waiters = vec![];
        for _ in 0..self.waiter_count.load(Ordering::Acquire) {
            waiters.push(None);
        }

        let mut queue: BTreeMap<Timestamp, Vec<usize>> = BTreeMap::new();
        let mut running = waiters.len();
        let mut open_tasks = 0;
        while let Some(event) = self.rx.recv().await {
            match event {
                ClockEvent::Wait { actor, until, done } => {
                    if waiters[actor].replace(done).is_some() {
                        panic!("An actor has somehow managed to wait twice");
                    }
                    running -= 1;
                    queue.entry(until).or_default().push(actor);
                    while running == 0 && open_tasks == 0 {
                        // advance time
                        let (timestamp, waiter_ids) = queue.pop_first().unwrap();
                        self.time.store(timestamp, Ordering::Release);

                        for id in waiter_ids {
                            let Some(waiter) = waiters[id].take() else {
                                continue;
                            };
                            running += 1;
                            let _ = waiter.send(());
                        }
                    }
                }
                ClockEvent::CancelWait { actor } => {
                    if waiters[actor].take().is_some() {
                        running += 1;
                    }
                }
                ClockEvent::StartTask => {
                    open_tasks += 1;
                }
                ClockEvent::FinishTask => {
                    open_tasks -= 1;
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum ClockEvent {
    Wait {
        actor: usize,
        until: Timestamp,
        done: oneshot::Sender<()>,
    },
    CancelWait {
        actor: usize,
    },
    StartTask,
    FinishTask,
}
