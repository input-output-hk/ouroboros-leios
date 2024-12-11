use std::{
    collections::BTreeMap,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};
use tokio::sync::{mpsc, oneshot, Mutex};

use super::timestamp::{AtomicTimestamp, Timestamp};

pub struct ClockBarrier {
    id: usize,
    time: Arc<AtomicTimestamp>,
    state: Arc<Mutex<ClockBarrierState>>,
    cancel: mpsc::UnboundedSender<usize>,
    pending_tasks: Arc<AtomicUsize>,
}

impl ClockBarrier {
    pub(crate) async fn new(
        time: Arc<AtomicTimestamp>,
        state: Arc<Mutex<ClockBarrierState>>,
    ) -> Self {
        let (id, cancel, pending_tasks) = state.lock().await.connect();
        Self {
            id,
            time,
            state,
            cancel,
            pending_tasks,
        }
    }
    pub fn now(&self) -> Timestamp {
        self.time.load(Ordering::Acquire)
    }

    /// Begin tracking a task which you expect to complete synchronously.
    /// No time will pass until all tasks have been finished.
    pub fn start_task(&self) {
        self.pending_tasks.fetch_add(1, Ordering::AcqRel);
    }

    /// Mark a synchronous task as completed.
    /// When all pending tasks have been finished, time may pass.
    pub fn finish_task(&self) {
        let old_task_count = self.pending_tasks.fetch_sub(1, Ordering::AcqRel);
        assert!(old_task_count != 0, "pending task count is out of sync");
    }

    pub async fn wait_until(&mut self, timestamp: Timestamp) {
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

        if self.now() < timestamp {
            let mut guard = WaitGuard(&self.cancel, Some(self.id));

            let rx = {
                let mut state = self.state.lock().await;
                state.wait(self.id, timestamp)
            };

            rx.await.unwrap();
            guard.defuse();
        }
        assert!(self.now() == timestamp);
    }
}

pub(crate) struct ClockBarrierState {
    time: Arc<AtomicTimestamp>,
    waiters: Vec<Option<oneshot::Sender<()>>>,
    waiting: usize,
    pending_tasks: Arc<AtomicUsize>,
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
            pending_tasks: Arc::new(AtomicUsize::new(0)),
            queue: BTreeMap::new(),
            cancel_tx,
            cancel_rx,
        }
    }

    fn connect(&mut self) -> (usize, mpsc::UnboundedSender<usize>, Arc<AtomicUsize>) {
        let id = self.waiters.len();
        self.waiters.push(None);
        (id, self.cancel_tx.clone(), self.pending_tasks.clone())
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
        while self.waiting == self.waiters.len() && self.pending_tasks.load(Ordering::Acquire) == 0
        {
            let (timestamp, waiters) = self.queue.pop_first().unwrap();
            self.time.store(timestamp, Ordering::Release);

            for id in waiters {
                let Some(waiter) = self.waiters[id].take() else {
                    continue;
                };
                self.waiting -= 1;
                let _ = waiter.send(());
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
