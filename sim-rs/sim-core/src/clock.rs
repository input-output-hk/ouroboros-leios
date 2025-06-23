use std::{
    cmp::Reverse,
    future::Future,
    pin::Pin,
    sync::{atomic::AtomicUsize, Arc},
    task::{Context, Poll},
    time::Duration,
};

pub use coordinator::ClockCoordinator;
use coordinator::ClockEvent;
use futures::FutureExt;
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
    timestamp_resolution: Duration,
    time: Arc<AtomicTimestamp>,
    waiters: Arc<AtomicUsize>,
    tasks: Arc<AtomicUsize>,
    tx: mpsc::UnboundedSender<ClockEvent>,
}

impl Clock {
    fn new(
        timestamp_resolution: Duration,
        time: Arc<AtomicTimestamp>,
        waiters: Arc<AtomicUsize>,
        tasks: Arc<AtomicUsize>,
        tx: mpsc::UnboundedSender<ClockEvent>,
    ) -> Self {
        Self {
            timestamp_resolution,
            time,
            waiters,
            tasks,
            tx,
        }
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
            timestamp_resolution: self.timestamp_resolution,
            time: self.time.clone(),
            tasks: self.tasks.clone(),
            tx: self.tx.clone(),
        }
    }
}

pub struct ClockBarrier {
    id: usize,
    timestamp_resolution: Duration,
    time: Arc<AtomicTimestamp>,
    tasks: Arc<AtomicUsize>,
    tx: mpsc::UnboundedSender<ClockEvent>,
}

impl ClockBarrier {
    pub fn now(&self) -> Timestamp {
        self.time.load(std::sync::atomic::Ordering::Acquire)
    }

    pub fn start_task(&self) {
        self.tasks.fetch_add(1, std::sync::atomic::Ordering::AcqRel);
    }

    pub fn finish_task(&self) {
        let _ = self.tx.send(ClockEvent::FinishTask);
    }

    pub fn wait_until(&mut self, timestamp: Timestamp) -> Waiter {
        self.wait(Some(timestamp.with_resolution(self.timestamp_resolution)))
    }

    pub fn wait_forever(&mut self) -> Waiter {
        self.wait(None)
    }

    fn wait(&mut self, until: Option<Timestamp>) -> Waiter {
        let (tx, rx) = oneshot::channel();
        let done = until.is_some_and(|ts| ts == self.now())
            || self
                .tx
                .send(ClockEvent::Wait {
                    actor: self.id,
                    until,
                    done: tx,
                })
                .is_err();

        Waiter {
            id: self.id,
            tx: &self.tx,
            rx,
            done,
        }
    }
}

pub struct Waiter<'a> {
    id: usize,
    tx: &'a mpsc::UnboundedSender<ClockEvent>,
    rx: oneshot::Receiver<()>,
    done: bool,
}

impl Future for Waiter<'_> {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.done {
            return Poll::Ready(());
        }
        match self.rx.poll_unpin(cx) {
            Poll::Pending => Poll::Pending,
            Poll::Ready(result) => {
                if result.is_ok() {
                    self.done = true;
                }
                Poll::Ready(())
            }
        }
    }
}

impl Drop for Waiter<'_> {
    fn drop(&mut self) {
        if !self.done {
            let _ = self.tx.send(ClockEvent::CancelWait { actor: self.id });
        }
    }
}
