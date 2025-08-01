use std::{
    collections::BTreeMap,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    time::Duration,
};

use tokio::sync::{mpsc, oneshot};

use crate::clock::TaskInitiator;

use super::{Clock, Timestamp, timestamp::AtomicTimestamp};

pub struct ClockCoordinator {
    timestamp_resolution: Duration,
    time: Arc<AtomicTimestamp>,
    tx: mpsc::UnboundedSender<ClockEvent>,
    rx: mpsc::UnboundedReceiver<ClockEvent>,
    waiter_count: Arc<AtomicUsize>,
    tasks: Arc<AtomicUsize>,
}

impl ClockCoordinator {
    pub fn new(timestamp_resolution: Duration) -> Self {
        let time = Arc::new(AtomicTimestamp::new(Timestamp::zero()));
        let (tx, rx) = mpsc::unbounded_channel();
        let waiter_count = Arc::new(AtomicUsize::new(0));
        let tasks = Arc::new(AtomicUsize::new(0));
        Self {
            timestamp_resolution,
            time,
            tx,
            rx,
            waiter_count,
            tasks,
        }
    }

    pub fn clock(&self) -> Clock {
        Clock::new(
            self.timestamp_resolution,
            self.time.clone(),
            self.waiter_count.clone(),
            TaskInitiator::new(self.tasks.clone()),
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
        while let Some(event) = self.rx.recv().await {
            match event {
                ClockEvent::Wait { actor, until, done } => {
                    assert!(until.is_none_or(|t| t >= self.time.load(Ordering::Acquire)));
                    if waiters[actor].replace(Waiter { until, done }).is_some() {
                        panic!("An actor has somehow managed to wait twice");
                    }
                    running = running.checked_sub(1).unwrap();
                    if let Some(timestamp) = until {
                        queue.entry(timestamp).or_default().push(actor);
                    }
                    while running == 0 && self.tasks.load(Ordering::Acquire) == 0 {
                        // advance time
                        let (timestamp, waiter_ids) = queue.pop_first().unwrap();
                        self.time.store(timestamp, Ordering::Release);

                        for id in waiter_ids {
                            if waiters[id]
                                .as_ref()
                                .and_then(|w| w.until)
                                .is_some_and(|ts| ts == timestamp)
                            {
                                running += 1;
                                let waiter = waiters[id].take().unwrap();
                                let _ = waiter.done.send(());
                            }
                        }
                    }
                }
                ClockEvent::CancelWait { actor } => {
                    if waiters[actor].take().is_some() {
                        running += 1;
                    }
                }
                ClockEvent::FinishTask => {
                    let prev_tasks = self.tasks.fetch_sub(1, Ordering::AcqRel);
                    assert!(prev_tasks != 0, "Finished a task that was never started");
                    assert!(
                        running != 0,
                        "All tasks were completed while there were no actors to complete them"
                    );
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
    FinishTask,
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
