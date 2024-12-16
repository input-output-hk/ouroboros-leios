use std::{
    cmp::Reverse,
    sync::{atomic::AtomicUsize, Arc},
};

pub use coordinator::ClockCoordinator;
use coordinator::ClockEvent;
use timestamp::AtomicTimestamp;
pub use timestamp::Timestamp;
use tokio::sync::{mpsc, oneshot};

mod coordinator;
mod timestamp;

// wrapper struct which holds a SimulationEvent,
// but is ordered by a timestamp (in reverse)
#[derive(Clone)]
pub(crate) struct FutureEvent<T>(pub Timestamp, pub T);
impl<T> FutureEvent<T> {
    fn key(&self) -> Reverse<Timestamp> {
        Reverse(self.0)
    }
}

impl<T> PartialEq for FutureEvent<T> {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl<T> Eq for FutureEvent<T> {}

impl<T> PartialOrd for FutureEvent<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for FutureEvent<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}

#[derive(Clone)]
pub struct Clock {
    time: Arc<AtomicTimestamp>,
    waiters: Arc<AtomicUsize>,
    tx: mpsc::UnboundedSender<ClockEvent>,
}

impl Clock {
    fn new(
        time: Arc<AtomicTimestamp>,
        waiters: Arc<AtomicUsize>,
        tx: mpsc::UnboundedSender<ClockEvent>,
    ) -> Self {
        Self { time, waiters, tx }
    }

    pub fn now(&self) -> Timestamp {
        self.time.load(std::sync::atomic::Ordering::Acquire)
    }

    pub fn barrier(&self) -> ClockBarrier {
        let id = self
            .waiters
            .fetch_add(1, std::sync::atomic::Ordering::AcqRel);
        ClockBarrier {
            id,
            time: self.time.clone(),
            tx: self.tx.clone(),
        }
    }
}

pub struct ClockBarrier {
    id: usize,
    time: Arc<AtomicTimestamp>,
    tx: mpsc::UnboundedSender<ClockEvent>,
}

impl ClockBarrier {
    pub fn now(&self) -> Timestamp {
        self.time.load(std::sync::atomic::Ordering::Acquire)
    }

    pub fn start_task(&self) {
        let _ = self.tx.send(ClockEvent::StartTask);
    }

    pub fn finish_task(&self) {
        let _ = self.tx.send(ClockEvent::FinishTask);
    }

    pub async fn wait_until(&mut self, timestamp: Timestamp) {
        let (tx, rx) = oneshot::channel();
        if self
            .tx
            .send(ClockEvent::Wait {
                actor: self.id,
                until: timestamp,
                done: tx,
            })
            .is_err()
        {
            return;
        }

        struct Guard<'a> {
            id: usize,
            tx: &'a mpsc::UnboundedSender<ClockEvent>,
        }
        impl Drop for Guard<'_> {
            fn drop(&mut self) {
                let _ = self.tx.send(ClockEvent::CancelWait { actor: self.id });
            }
        }

        let guard = Guard {
            id: self.id,
            tx: &self.tx,
        };
        if rx.await.is_ok() {
            assert_eq!(self.now(), timestamp);
            std::mem::forget(guard);    
        }
    }
}
