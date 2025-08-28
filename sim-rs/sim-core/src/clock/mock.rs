use std::{
    collections::HashMap,
    sync::{Arc, atomic::AtomicUsize},
    time::Duration,
};

use tokio::sync::{mpsc, oneshot};

use crate::clock::{
    Clock, TaskInitiator, Timestamp, coordinator::ClockEvent, timestamp::AtomicTimestamp,
};

pub struct MockClockCoordinator {
    time: Arc<AtomicTimestamp>,
    tx: mpsc::UnboundedSender<ClockEvent>,
    rx: mpsc::UnboundedReceiver<ClockEvent>,
    waiter_count: Arc<AtomicUsize>,
    tasks: Arc<AtomicUsize>,
    waiters: HashMap<usize, Waiter>,
}

impl Default for MockClockCoordinator {
    fn default() -> Self {
        Self::new()
    }
}

impl MockClockCoordinator {
    pub fn new() -> Self {
        let time = Arc::new(AtomicTimestamp::new(Timestamp::zero()));
        let (tx, rx) = mpsc::unbounded_channel();
        let waiter_count = Arc::new(AtomicUsize::new(0));
        let tasks = Arc::new(AtomicUsize::new(0));
        Self {
            time,
            tx,
            rx,
            waiter_count,
            tasks,
            waiters: HashMap::new(),
        }
    }

    pub fn clock(&self) -> Clock {
        Clock::new(
            Duration::from_nanos(1),
            self.time.clone(),
            self.waiter_count.clone(),
            TaskInitiator::new(self.tasks.clone()),
            self.tx.clone(),
        )
    }

    pub fn advance_time(&mut self, until: Timestamp) {
        while let Ok(event) = self.rx.try_recv() {
            match event {
                ClockEvent::Wait { actor, until, done } => {
                    if self.waiters.insert(actor, Waiter { until, done }).is_some() {
                        panic!("waiter {actor} waited twice");
                    }
                }
                ClockEvent::CancelWait { actor } => {
                    if self.waiters.remove(&actor).is_none() {
                        panic!("waiter {actor} cancelled a wait twice");
                    }
                }
                ClockEvent::FinishTask => {
                    if self.tasks.fetch_sub(1, std::sync::atomic::Ordering::AcqRel) == 0 {
                        panic!("cancelled too many tasks");
                    }
                }
            }
        }
        assert_eq!(
            self.waiters.len(),
            self.waiter_count.load(std::sync::atomic::Ordering::Acquire),
            "not every worker is waiting for time to pass"
        );

        self.time.store(until, std::sync::atomic::Ordering::Release);
        self.waiters = std::mem::take(&mut self.waiters)
            .into_iter()
            .filter_map(|(actor, waiter)| {
                if let Some(t) = &waiter.until {
                    if *t < until {
                        panic!("advanced time too far (waited for {until:?}, next event at {t:?})");
                    }
                    if *t == until {
                        let _ = waiter.done.send(());
                        return None;
                    }
                }
                Some((actor, waiter))
            })
            .collect();
    }
}

struct Waiter {
    until: Option<Timestamp>,
    done: oneshot::Sender<()>,
}
