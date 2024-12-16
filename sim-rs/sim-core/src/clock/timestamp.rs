use std::{
    ops::{Add, Sub},
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};

use serde::Serialize;

/// A timestamp tracks the time from the start of the simulation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Timestamp(Duration);

impl Timestamp {
    pub fn zero() -> Self {
        Self(Duration::from_secs(0))
    }
}

impl From<Duration> for Timestamp {
    fn from(value: Duration) -> Self {
        Self(value)
    }
}

impl Add<Duration> for Timestamp {
    type Output = Timestamp;

    fn add(self, rhs: Duration) -> Self::Output {
        Timestamp(self.0 + rhs)
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

pub struct AtomicTimestamp(AtomicU64);
impl AtomicTimestamp {
    pub fn new(val: Timestamp) -> Self {
        Self(AtomicU64::new(duration_to_u64(val.0)))
    }
    pub fn load(&self, order: Ordering) -> Timestamp {
        let val = self.0.load(order);
        Timestamp(u64_to_duration(val))
    }

    pub fn store(&self, val: Timestamp, order: Ordering) {
        let val = duration_to_u64(val.0);
        self.0.store(val, order);
    }
}

fn u64_to_duration(val: u64) -> Duration {
    Duration::from_nanos(val)
}

fn duration_to_u64(val: Duration) -> u64 {
    val.as_nanos() as u64
}
