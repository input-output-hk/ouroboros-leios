use std::{
    ops::{Add, AddAssign, Sub},
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};

use serde::Serialize;

const NANOS_PER_SEC: u64 = 1_000_000_000;

/// A timestamp tracks the time from the start of the simulation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Timestamp(u64);

impl Timestamp {
    pub fn zero() -> Self {
        Self(0)
    }

    pub fn from_secs(secs: u64) -> Self {
        Self(secs * NANOS_PER_SEC)
    }

    pub fn checked_sub_duration(self, rhs: Duration) -> Option<Self> {
        Some(Self(self.0.checked_sub(rhs.as_nanos() as u64)?))
    }

    pub fn with_resolution(self, delta: Duration) -> Self {
        Self(self.0.next_multiple_of(delta.as_nanos() as u64))
    }
}

impl Add<Duration> for Timestamp {
    type Output = Timestamp;

    fn add(self, rhs: Duration) -> Self::Output {
        Self(self.0 + rhs.as_nanos() as u64)
    }
}

impl AddAssign<Duration> for Timestamp {
    fn add_assign(&mut self, rhs: Duration) {
        self.0 += rhs.as_nanos() as u64;
    }
}

impl Sub<Timestamp> for Timestamp {
    type Output = Duration;

    fn sub(self, rhs: Timestamp) -> Self::Output {
        Duration::from_nanos(self.0 - rhs.0)
    }
}

impl Sub<Duration> for Timestamp {
    type Output = Timestamp;

    fn sub(self, rhs: Duration) -> Self::Output {
        Self(self.0 - rhs.as_nanos() as u64)
    }
}

impl Serialize for Timestamp {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_f64(self.0 as f64 / NANOS_PER_SEC as f64)
    }
}

pub struct AtomicTimestamp(AtomicU64);
impl AtomicTimestamp {
    pub fn new(val: Timestamp) -> Self {
        Self(AtomicU64::new(val.0))
    }
    pub fn load(&self, order: Ordering) -> Timestamp {
        Timestamp(self.0.load(order))
    }

    pub fn store(&self, val: Timestamp, order: Ordering) {
        self.0.store(val.0, order);
    }
}
