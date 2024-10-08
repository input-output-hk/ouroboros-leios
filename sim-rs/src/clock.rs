use std::{
    ops::Add,
    time::{Duration, Instant},
};

use serde::Serialize;
use tokio::time::{self, Sleep};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Timestamp(Duration);
impl Add<Duration> for Timestamp {
    type Output = Timestamp;

    fn add(self, rhs: Duration) -> Self::Output {
        Timestamp(self.0 + rhs)
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

#[derive(Clone)]
pub struct Clock {
    start: Instant,
}

impl Clock {
    pub fn new(start: Instant) -> Self {
        Self { start }
    }

    pub fn now(&self) -> Timestamp {
        Timestamp(self.start.elapsed())
    }

    pub fn wait_until(&self, timestamp: Timestamp) -> Sleep {
        let instant = self.start + timestamp.0;
        time::sleep_until(instant.into())
    }
}
