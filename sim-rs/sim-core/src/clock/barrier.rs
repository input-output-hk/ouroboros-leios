use std::{
    collections::BTreeMap,
    sync::{atomic::Ordering, Arc},
};
use tokio::sync::{mpsc, oneshot, Mutex};
use tracing::debug;

use super::timestamp::{AtomicTimestamp, Timestamp};

pub struct ClockBarrier {
    id: usize,
    time: Arc<AtomicTimestamp>,
    state: Arc<Mutex<ClockBarrierState>>,
    cancel: mpsc::UnboundedSender<usize>,
}

impl ClockBarrier {
    pub(crate) async fn new(
        time: Arc<AtomicTimestamp>,
        state: Arc<Mutex<ClockBarrierState>>,
    ) -> Self {
        let (id, cancel) = state.lock().await.connect();
        Self {
            id,
            time,
            state,
            cancel,
        }
    }
    pub fn now(&self) -> Timestamp {
        self.time.load(Ordering::Relaxed)
    }

    pub async fn wait_until(&mut self, timestamp: Timestamp) {
        let now = self.time.load(Ordering::Relaxed);
        if timestamp <= now {
            debug!("not sleeping because {timestamp:?} <= {now:?}");
            return;
        }

        let rx = {
            let mut state = self.state.lock().await;
            state.wait(self.id, timestamp)
        };

        struct WaitGuard<'a>(&'a mpsc::UnboundedSender<usize>, Option<usize>);
        impl WaitGuard<'_> {
            fn defuse(&mut self) {
                self.1 = None;
            }
        }
        impl Drop for WaitGuard<'_> {
            fn drop(&mut self) {
                if let Some(id) = self.1.take() {
                    let _ = self.0.send(id);
                }
            }
        }

        let mut guard = WaitGuard(&self.cancel, Some(self.id));
        rx.await.unwrap();
        guard.defuse();
    }
}

pub(crate) struct ClockBarrierState {
    time: Arc<AtomicTimestamp>,
    waiters: Vec<Option<oneshot::Sender<()>>>,
    waiting: usize,
    queue: BTreeMap<Timestamp, Vec<usize>>,
    cancel_tx: mpsc::UnboundedSender<usize>,
    cancel_rx: mpsc::UnboundedReceiver<usize>,
}
impl ClockBarrierState {
    pub fn new(time: Arc<AtomicTimestamp>) -> Self {
        let (cancel_tx, cancel_rx) = mpsc::unbounded_channel();
        Self {
            time,
            waiters: vec![],
            waiting: 0,
            queue: BTreeMap::new(),
            cancel_tx,
            cancel_rx,
        }
    }

    fn connect(&mut self) -> (usize, mpsc::UnboundedSender<usize>) {
        let id = self.waiters.len();
        self.waiters.push(None);
        (id, self.cancel_tx.clone())
    }

    fn wait(&mut self, id: usize, until: Timestamp) -> oneshot::Receiver<()> {
        self.flush_cancelled_waiters();

        // queue this to run later
        let (tx, rx) = oneshot::channel();
        if self.waiters[id].replace(tx).is_some() {
            panic!("how did you wait twice");
        }
        self.queue.entry(until).or_default().push(id);
        self.waiting += 1;

        self.flush_cancelled_waiters();
        while self.waiting == self.waiters.len() {
            let (timestamp, waiters) = self.queue.pop_first().unwrap();
            self.time.store(timestamp, Ordering::Relaxed);

            for id in waiters {
                let Some(waiter) = self.waiters[id].take() else {
                    continue;
                };
                if waiter.send(()).is_ok() {
                    self.waiting -= 1;
                }
            }
        }

        rx
    }

    fn flush_cancelled_waiters(&mut self) {
        while let Ok(cancelled) = self.cancel_rx.try_recv() {
            if self.waiters[cancelled].take().is_some() {
                self.waiting -= 1;
            }
        }
    }
}
