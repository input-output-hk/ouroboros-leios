use std::{cmp::Reverse, sync::Arc};

pub use barrier::ClockBarrier;
use barrier::ClockBarrierState;
use timestamp::AtomicTimestamp;
pub use timestamp::Timestamp;
use tokio::sync::Mutex;

mod barrier;
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
    inner: Arc<Mutex<ClockBarrierState>>,
}

impl Default for Clock {
    fn default() -> Self {
        Self::new()
    }
}

impl Clock {
    pub fn new() -> Self {
        let time = Arc::new(AtomicTimestamp::new(Timestamp::zero()));
        let inner = Arc::new(Mutex::new(ClockBarrierState::new(time.clone())));
        Self { time, inner }
    }

    pub fn now(&self) -> Timestamp {
        self.time.load(std::sync::atomic::Ordering::Acquire)
    }

    pub async fn barrier(&self) -> ClockBarrier {
        ClockBarrier::new(self.time.clone(), self.inner.clone()).await
    }
}
