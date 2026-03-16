use std::{
    collections::BTreeMap,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    time::Duration,
};

use tokio::{
    select,
    sync::{Notify, mpsc, oneshot},
};

use crate::clock::TaskInitiator;

use super::{Clock, Timestamp, timestamp::AtomicTimestamp};

/// Other shards' time references for computing the lookahead ceiling.
pub struct PeerShard {
    /// The peer shard's current time.
    pub time: Arc<AtomicTimestamp>,
    /// Minimum network latency from that shard to this one.
    pub min_latency: Duration,
    /// Notified when the peer advances time.
    pub time_advanced: Arc<Notify>,
}

pub struct ClockCoordinator {
    timestamp_resolution: Duration,
    time: Arc<AtomicTimestamp>,
    time_ceiling: Arc<AtomicTimestamp>,
    peer_shards: Vec<PeerShard>,
    tx: mpsc::UnboundedSender<ClockEvent>,
    rx: mpsc::UnboundedReceiver<ClockEvent>,
    waiter_count: Arc<AtomicUsize>,
    tasks: Arc<AtomicUsize>,
    task_notify: Arc<Notify>,
    /// Notified whenever this coordinator advances time, so external
    /// observers (e.g. the cross-shard broker) can react.
    time_advanced_notify: Arc<Notify>,
}

impl ClockCoordinator {
    pub fn new(timestamp_resolution: Duration) -> Self {
        let time = Arc::new(AtomicTimestamp::new(Timestamp::zero()));
        let time_ceiling = Arc::new(AtomicTimestamp::new(Timestamp::max()));
        let (tx, rx) = mpsc::unbounded_channel();
        let waiter_count = Arc::new(AtomicUsize::new(0));
        let tasks = Arc::new(AtomicUsize::new(0));
        let task_notify = Arc::new(Notify::new());
        let time_advanced_notify = Arc::new(Notify::new());
        Self {
            timestamp_resolution,
            time,
            time_ceiling,
            peer_shards: Vec::new(),
            tx,
            rx,
            waiter_count,
            tasks,
            task_notify,
            time_advanced_notify,
        }
    }

    /// Returns a shared reference to this coordinator's time, readable from other shards.
    pub fn shared_time(&self) -> Arc<AtomicTimestamp> {
        self.time.clone()
    }

    /// Returns the time ceiling, which external code can update to prevent
    /// this coordinator from advancing past a certain timestamp.
    pub fn time_ceiling(&self) -> Arc<AtomicTimestamp> {
        self.time_ceiling.clone()
    }

    /// Returns a Notify that can be used to wake this coordinator
    /// when the time ceiling changes.
    pub fn ceiling_notify(&self) -> Arc<Notify> {
        self.task_notify.clone()
    }

    /// Returns a Notify that fires whenever this coordinator advances time.
    pub fn time_advanced_notify(&self) -> Arc<Notify> {
        self.time_advanced_notify.clone()
    }

    /// Set peer shards for lookahead ceiling computation.
    pub fn set_peer_shards(&mut self, peers: Vec<PeerShard>) {
        self.peer_shards = peers;
    }

    pub fn clock(&self) -> Clock {
        Clock::new(
            self.timestamp_resolution,
            self.time.clone(),
            self.waiter_count.clone(),
            TaskInitiator::new(self.tasks.clone()),
            self.tx.clone(),
            self.task_notify.clone(),
        )
    }

    pub async fn run(&mut self) {
        let mut waiters = vec![];
        for _ in 0..self.waiter_count.load(Ordering::Acquire) {
            waiters.push(None);
        }

        let mut queue: BTreeMap<Timestamp, Vec<usize>> = BTreeMap::new();
        let mut running = waiters.len();
        loop {
            // If all actors are waiting, wait for either a new event or a task completion
            if running == 0 {
                loop {
                    // Register interest in notifications BEFORE checking,
                    // to avoid missing a notify between the check and the await.
                    let task_notified = self.task_notify.notified();
                    tokio::pin!(task_notified);
                    let peer_notified: Vec<_> = self.peer_shards
                        .iter()
                        .map(|p| Box::pin(p.time_advanced.notified()))
                        .collect();
                    let has_peers = !peer_notified.is_empty();

                    // Try to advance time if tasks are done
                    while running == 0 && self.tasks.load(Ordering::Acquire) == 0 {
                        let Some((timestamp, _)) = queue.first_key_value() else {
                            break;
                        };
                        let timestamp = *timestamp;
                        // Compute ceiling: min of external ceiling and peer shard lookaheads
                        let mut ceiling = self.time_ceiling.load(Ordering::Acquire);
                        for peer in &self.peer_shards {
                            let peer_time = peer.time.load(Ordering::Acquire);
                            let lookahead = peer_time + peer.min_latency;
                            if lookahead < ceiling {
                                ceiling = lookahead;
                            }
                        }
                        if timestamp > ceiling {
                            break;
                        }
                        let (_, waiter_ids) = queue.pop_first().unwrap();
                        self.time.store(timestamp, Ordering::Release);
                        self.time_advanced_notify.notify_waiters();

                        for id in waiter_ids {
                            if waiters[id]
                                .as_ref()
                                .and_then(|w: &Waiter| w.until)
                                .is_some_and(|ts| ts == timestamp)
                            {
                                running += 1;
                                let waiter = waiters[id].take().unwrap();
                                let _ = waiter.done.send(());
                            }
                        }
                    }
                    if running != 0 {
                        break;
                    }
                    // Blocked — wait for a channel event, task completion, or peer advancement
                    select! {
                        event = self.rx.recv() => {
                            let Some(event) = event else { return };
                            Self::handle_event(event, &mut waiters, &mut running, &mut queue, &self.time);
                        }
                        () = &mut task_notified => {
                            continue;
                        }
                        _ = futures::future::select_all(peer_notified), if has_peers => {
                            continue;
                        }
                    }
                }
            }

            // Actors are running — just process channel events
            let Some(event) = self.rx.recv().await else {
                return;
            };
            Self::handle_event(event, &mut waiters, &mut running, &mut queue, &self.time);
        }
    }

    fn handle_event(
        event: ClockEvent,
        waiters: &mut [Option<Waiter>],
        running: &mut usize,
        queue: &mut BTreeMap<Timestamp, Vec<usize>>,
        time: &AtomicTimestamp,
    ) {
        match event {
            ClockEvent::Wait { actor, until, done } => {
                // If time has advanced past the requested wait (due to the
                // finish_task atomic+notify race), treat as a normal wait at
                // the current time — it will be immediately woken by the
                // time advancement loop.
                let now = time.load(Ordering::Acquire);
                let until = if until.is_some_and(|t| t < now) {
                    Some(now)
                } else {
                    until
                };
                if waiters[actor].replace(Waiter { until, done }).is_some() {
                    panic!("An actor has somehow managed to wait twice");
                }
                *running = running.checked_sub(1).unwrap();
                if let Some(timestamp) = until {
                    queue.entry(timestamp).or_default().push(actor);
                }
            }
            ClockEvent::CancelWait { actor } => {
                if waiters[actor].take().is_some() {
                    *running += 1;
                }
            }
        }
    }
}

struct Waiter {
    until: Option<Timestamp>,
    done: oneshot::Sender<()>,
}

#[derive(Debug)]
pub enum ClockEvent {
    Wait {
        actor: usize,
        until: Option<Timestamp>,
        done: oneshot::Sender<()>,
    },
    CancelWait {
        actor: usize,
    },
}

#[cfg(test)]
mod tests {
    use std::{task::Poll, time::Duration};

    use futures::poll;
    use tokio::pin;

    use super::ClockCoordinator;

    const TIMESTAMP_RESOLUTION: Duration = Duration::from_nanos(1);

    #[tokio::test]
    async fn should_wait_once_all_workers_are_waiting() {
        let mut coordinator = ClockCoordinator::new(TIMESTAMP_RESOLUTION);
        let clock = coordinator.clock();
        let t0 = clock.now();
        let t1 = t0 + Duration::from_millis(5);
        let t2 = t0 + Duration::from_millis(10);
        let mut actor1 = clock.barrier();
        let mut actor2 = clock.barrier();

        let run_future = coordinator.run();
        pin!(run_future);

        let mut wait1 = actor1.wait_until(t1);
        assert_eq!(poll!(&mut wait1), Poll::Pending); // the wait is pending
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(clock.now(), t0); // no time has passed
        assert_eq!(poll!(&mut wait1), Poll::Pending); // the 5ms wait is still pending, because clock 2 isn't finished

        let mut wait2 = actor2.wait_until(t2);
        assert_eq!(poll!(&mut wait2), Poll::Pending);
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(clock.now(), t1); // 5ms have passed
        assert_eq!(poll!(&mut wait2), Poll::Pending); // the 10ms wait is still pending
        assert_eq!(poll!(wait1), Poll::Ready(())); // the 5ms wait is done
    }

    #[tokio::test]
    async fn should_cancel_wait_when_wait_future_is_dropped() {
        let mut coordinator = ClockCoordinator::new(TIMESTAMP_RESOLUTION);
        let clock = coordinator.clock();
        let t0 = clock.now();
        let t1 = t0 + Duration::from_millis(5);
        let mut actor1 = clock.barrier();
        let mut actor2 = clock.barrier();

        let run_future = coordinator.run();
        pin!(run_future);

        {
            let wait1 = actor1.wait_until(t1);
            assert_eq!(poll!(wait1), Poll::Pending); // the wait is pending
            // and now it goes out of scope and gets dropped
        }
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(clock.now(), t0); // no time has passed

        let mut wait2 = actor2.wait_until(t1);
        assert_eq!(poll!(&mut wait2), Poll::Pending);
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(clock.now(), t0); // no time has passed
        assert_eq!(poll!(&mut wait2), Poll::Pending); // the remaining wait is still pending
    }

    #[tokio::test]
    async fn should_avoid_race_condition() {
        let mut coordinator = ClockCoordinator::new(TIMESTAMP_RESOLUTION);
        let clock = coordinator.clock();
        let t0 = clock.now();
        let t1 = t0 + Duration::from_millis(5);
        let t2 = t0 + Duration::from_millis(10);
        let mut actor1 = clock.barrier();
        let mut actor2 = clock.barrier();

        let run_future = coordinator.run();
        pin!(run_future);

        // make actor 1 wait for a short time, then cancel it, then wait for a long time
        {
            let wait1 = actor1.wait_until(t1);
            assert_eq!(poll!(wait1), Poll::Pending);
        }
        let mut wait1 = actor1.wait_until(t2);
        assert_eq!(poll!(&mut wait1), Poll::Pending);
        assert_eq!(poll!(&mut run_future), Poll::Pending);
        assert_eq!(clock.now(), t0); // no time has passed
        assert_eq!(poll!(&mut wait1), Poll::Pending);

        let wait2 = actor2.wait_until(t2);
        assert_eq!(poll!(wait2), Poll::Pending);
        while let Poll::Pending = poll!(&mut wait1) {
            assert_eq!(poll!(&mut run_future), Poll::Pending);
        }
        // We expect a long time to have passed, because the "short" wait was cancelled
        assert_eq!(clock.now(), t2);
    }

    #[tokio::test]
    async fn should_allow_time_to_stand_still() {
        let mut coordinator = ClockCoordinator::new(TIMESTAMP_RESOLUTION);
        let clock = coordinator.clock();
        let t0 = clock.now();
        let t1 = t0 + Duration::from_millis(5);
        let t2 = t0 + Duration::from_millis(10);
        let mut actor = clock.barrier();

        let run_future = coordinator.run();
        pin!(run_future);

        // The actor waits until t1, then cancels that wait,
        // before the coordinator has a chance to run
        {
            let wait1 = actor.wait_until(t1);
            assert_eq!(poll!(wait1), Poll::Pending);
        }

        // The actor should be able to wait until t1 without issue,
        // even though it has already cancelled a wait for t1.
        let mut wait1 = actor.wait_until(t1);
        assert_eq!(poll!(&mut wait1), Poll::Pending);
        assert_eq!(poll!(&mut run_future), Poll::Pending);
        assert_eq!(poll!(&mut wait1), Poll::Ready(()));
        drop(wait1);

        // Test waiting for another few moments just for good measure
        let mut wait2 = actor.wait_until(t2);
        assert_eq!(poll!(&mut wait2), Poll::Pending);
        assert_eq!(poll!(&mut run_future), Poll::Pending);
        assert_eq!(poll!(&mut wait2), Poll::Ready(()));
    }

    #[tokio::test]
    async fn should_allow_waiting_forever() {
        let mut coordinator = ClockCoordinator::new(TIMESTAMP_RESOLUTION);
        let clock = coordinator.clock();
        let t0 = clock.now();
        let t1 = t0 + Duration::from_millis(5);
        let mut actor1 = clock.barrier();
        let mut actor2 = clock.barrier();

        let run_future = coordinator.run();
        pin!(run_future);

        let mut wait1 = actor1.wait_until(t1);
        assert_eq!(poll!(&mut wait1), Poll::Pending); // the wait is pending
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(clock.now(), t0); // no time has passed
        assert_eq!(poll!(&mut wait1), Poll::Pending); // the 5ms wait is still pending, because clock 2 isn't finished

        let mut wait2 = actor2.wait_forever();
        assert_eq!(poll!(&mut wait2), Poll::Pending);
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(clock.now(), t1); // 5ms have passed
        assert_eq!(poll!(&mut wait2), Poll::Pending); // the eternal wait is still pending
        assert_eq!(poll!(wait1), Poll::Ready(())); // the 5ms wait is done
    }
}
