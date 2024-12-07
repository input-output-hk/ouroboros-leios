use std::{
    cmp::Reverse,
    collections::BTreeMap,
    ops::{Add, Sub},
    sync::{atomic::AtomicUsize, Arc, Mutex},
    time::Duration,
};

use serde::Serialize;
use tokio::sync::oneshot;
use tracing::debug;

/// A timestamp tracks both the time from the start of the simulation and a unique number.
/// The number is used to order events that happen at the same time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Timestamp(Duration, usize);

/// This counter ensures that timestamps are unique.
///
/// We need this in the case of cancellation of a wait_until call.
static COUNTER: AtomicUsize = AtomicUsize::new(0);

impl Timestamp {
    pub fn zero() -> Self {
        Self(
            Duration::from_secs(0),
            COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        )
    }
}

impl From<Duration> for Timestamp {
    fn from(value: Duration) -> Self {
        Self(
            value,
            COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        )
    }
}

impl Add<Duration> for Timestamp {
    type Output = Timestamp;

    fn add(self, rhs: Duration) -> Self::Output {
        Timestamp(
            self.0 + rhs,
            COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        )
    }
}

impl Sub<Timestamp> for Timestamp {
    type Output = Duration;

    fn sub(self, rhs: Timestamp) -> Self::Output {
        self.0 - rhs.0
    }
}

impl Serialize for Timestamp {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u128(self.0.as_nanos())
    }
}

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
    inner: Arc<Mutex<ClockInner>>,
}

struct ClockInner {
    time: Duration,
    num_tasks: usize,
    calls: BTreeMap<Timestamp, oneshot::Sender<()>>,
}

impl Clock {
    pub fn new(num_tasks: usize) -> Self {
        Self {
            inner: Arc::new(Mutex::new(ClockInner {
                time: Duration::ZERO,
                num_tasks,
                calls: BTreeMap::new(),
            })),
        }
    }

    pub fn now(&self) -> Timestamp {
        let now = self.inner.lock().unwrap().time;
        Timestamp::from(now)
    }

    pub async fn wait_until(&self, timestamp: Timestamp) {
        let now = self.now();
        if timestamp <= now {
            debug!("not sleeping because {timestamp:?} <= {now:?}");
            return;
        }

        let (tx, mut rx) = oneshot::channel();

        {
            let mut this = self.inner.lock().unwrap();
            this.calls.insert(timestamp, tx);
            if this.calls.len() == this.num_tasks {
                this.time = this
                    .calls
                    .iter()
                    .next()
                    .map(|(t, _)| t.0)
                    .unwrap_or_default();
                while let Some((&Timestamp(t, _), _w)) = this.calls.iter().next() {
                    debug!("waking one task at {:?}", this.time);
                    if t != this.time {
                        break;
                    }
                    let ev = this.calls.pop_first().unwrap();
                    if ev.1.send(()).is_err() {
                        panic!("waker already sent: {:?}", this.time);
                    }
                }
            } else {
                debug!("not enough tasks to wake: {}", this.calls.len());
            }
        }

        // cancellation needs to remove the entry
        struct Guard<'a>(&'a Clock, Timestamp);
        impl<'a> Guard<'a> {
            fn defuse(&mut self) {
                self.1 .1 = 0;
            }
        }
        impl Drop for Guard<'_> {
            fn drop(&mut self) {
                if self.1 .1 == 0 {
                    return;
                }
                debug!("dropping guard for {:#?}", self.1);
                let mut this = self.0.inner.lock().unwrap();
                this.calls.remove(&self.1);
            }
        }

        // we need to ensure that `rx` is dropped after the guard, otherwise the channel will already
        // be closed when a concurrent wake-up occurs (this can happen when waking up some tasks at some
        // specific time, where one node sends to another that will then be woken up by the send and
        // thus cancel this async fn future)
        let rx = &mut rx;
        let mut guard = Guard(self, timestamp);

        debug!("waiting for waker to be triggered at {timestamp:?}");
        rx.await.unwrap();
        // avoid touching the lock when not needed
        guard.defuse();
    }
}
