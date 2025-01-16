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
                    if waiters[actor].replace(Waiter { until, done }).is_some() {
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
                            if waiter.until == timestamp {
                                running += 1;
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

struct Waiter {
    until: Timestamp,
    done: oneshot::Sender<()>,
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

#[cfg(test)]
mod tests {
    use std::{task::Poll, time::Duration};

    use futures::poll;
    use tokio::pin;

    use super::ClockCoordinator;

    #[tokio::test]
    async fn should_wait_once_all_workers_are_waiting() {
        let mut coordinator = ClockCoordinator::new();
        let clock = coordinator.clock();
        let t0 = clock.now();
        let t1 = t0 + Duration::from_millis(5);
        let t2 = t0 + Duration::from_millis(10);
        let mut actor1 = clock.barrier();
        let mut actor2 = clock.barrier();

        let run_future = coordinator.run();
        pin!(run_future);

        let wait1 = actor1.wait_until(t1);
        pin!(wait1);
        assert_eq!(poll!(&mut wait1), Poll::Pending); // the wait is pending
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(clock.now(), t0); // no time has passed
        assert_eq!(poll!(&mut wait1), Poll::Pending); // the 5ms wait is still pending, because clock 2 isn't finished

        let wait2 = actor2.wait_until(t2);
        pin!(wait2);
        assert_eq!(poll!(&mut wait2), Poll::Pending);
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(clock.now(), t1); // 5ms have passed
        assert_eq!(poll!(&mut wait2), Poll::Pending); // the 10ms wait is still pending
        assert_eq!(poll!(wait1), Poll::Ready(())); // the 5ms wait is done
    }

    #[tokio::test]
    async fn should_cancel_wait_when_wait_future_is_dropped() {
        let mut coordinator = ClockCoordinator::new();
        let clock = coordinator.clock();
        let t0 = clock.now();
        let t1 = t0 + Duration::from_millis(5);
        let mut actor1 = clock.barrier();
        let mut actor2 = clock.barrier();

        let run_future = coordinator.run();
        pin!(run_future);

        {
            let wait1 = actor1.wait_until(t1);
            pin!(wait1);
            assert_eq!(poll!(wait1), Poll::Pending); // the wait is pending
            // and now it goes out of scope and gets dropped
        }
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(clock.now(), t0); // no time has passed

        let wait2 = actor2.wait_until(t1);
        pin!(wait2);
        assert_eq!(poll!(&mut wait2), Poll::Pending);
        assert_eq!(poll!(&mut run_future), Poll::Pending); // try advancing time
        assert_eq!(clock.now(), t0); // no time has passed
        assert_eq!(poll!(&mut wait2), Poll::Pending); // the remaining wait is still pending
    }

    #[tokio::test]
    async fn should_avoid_race_condition() {
        let mut coordinator = ClockCoordinator::new();
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
            pin!(wait1);
            assert_eq!(poll!(wait1), Poll::Pending);
        }
        let wait1 = actor1.wait_until(t2);
        pin!(wait1);
        assert_eq!(poll!(&mut wait1), Poll::Pending);
        assert_eq!(poll!(&mut run_future), Poll::Pending);
        assert_eq!(clock.now(), t0); // no time has passed
        assert_eq!(poll!(&mut wait1), Poll::Pending);

        let wait2 = actor2.wait_until(t2);
        pin!(wait2);
        assert_eq!(poll!(wait2), Poll::Pending);
        while let Poll::Pending = poll!(&mut wait1) {
            assert_eq!(poll!(&mut run_future), Poll::Pending);
        }
        // We expect a long time to have passed, because the "short" wait was cancelled
        assert_eq!(clock.now(), t2);
    }
}
