use std::{
    ops::{Add, Sub},
    time::{Duration, Instant},
};

use serde::Serialize;
use tokio::time;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Timestamp(Duration);
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

#[derive(Clone)]
pub struct Clock {
    start: Instant,
    scale: f64,
}

impl Clock {
    pub fn new(start: Instant, scale: f64) -> Self {
        Self { start, scale }
    }

    pub fn now(&self) -> Timestamp {
        let duration = self.start.elapsed();
        let scaled = Duration::from_secs_f64(duration.as_secs_f64() * self.scale);
        Timestamp(scaled)
    }

    pub async fn wait_until(&self, timestamp: Timestamp) {
        let scaled = Duration::from_secs_f64(timestamp.0.as_secs_f64() / self.scale);
        let instant = self.start + scaled;
        if instant > Instant::now() {
            time::sleep_until(instant.into()).await;
        }
    }
}
