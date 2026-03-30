//! Slot clock: maps wall-clock time to slot numbers and produces an aligned
//! tick stream.
//!
//! The clock recomputes the slot from `(now - genesis_time) / slot_duration`
//! on each tick, avoiding drift accumulation.

use std::time::{Duration, SystemTime, UNIX_EPOCH};

use tokio::time::{Instant, Interval};

/// A real-time slot clock anchored to a genesis timestamp.
pub struct SlotClock {
    /// Genesis time as a `SystemTime`.
    genesis: SystemTime,
    /// Duration of one slot.
    slot_duration: Duration,
    /// Tokio interval aligned to slot boundaries.
    interval: Interval,
}

impl SlotClock {
    /// Create a new slot clock.
    ///
    /// `genesis_time_unix` is the Unix timestamp (seconds) of slot 0.
    /// `slot_duration_ms` is the slot length in milliseconds.
    pub fn new(genesis_time_unix: u64, slot_duration_ms: u64) -> Self {
        let genesis = UNIX_EPOCH + Duration::from_secs(genesis_time_unix);
        let slot_duration = Duration::from_millis(slot_duration_ms);

        // Compute when the next slot boundary occurs.
        let now = SystemTime::now();
        let next_boundary = Self::next_slot_boundary(now, genesis, slot_duration);

        // Convert SystemTime offset into a tokio Instant.
        let until_next = next_boundary.duration_since(now).unwrap_or(Duration::ZERO);
        let start = Instant::now() + until_next;

        let interval = tokio::time::interval_at(start, slot_duration);

        Self {
            genesis,
            slot_duration,
            interval,
        }
    }

    /// Returns the current slot number based on wall-clock time.
    pub fn current_slot(&self) -> u64 {
        let now = SystemTime::now();
        let elapsed = now.duration_since(self.genesis).unwrap_or(Duration::ZERO);
        elapsed.as_millis() as u64 / self.slot_duration.as_millis() as u64
    }

    /// Wait for the next slot tick and return the new slot number.
    pub async fn tick(&mut self) -> u64 {
        self.interval.tick().await;
        self.current_slot()
    }

    /// Compute the next slot boundary at or after `now`.
    fn next_slot_boundary(
        now: SystemTime,
        genesis: SystemTime,
        slot_duration: Duration,
    ) -> SystemTime {
        let elapsed = now.duration_since(genesis).unwrap_or(Duration::ZERO);
        let slot_ms = slot_duration.as_millis() as u64;
        let elapsed_ms = elapsed.as_millis() as u64;

        // Slots elapsed (truncated), then the start of the *next* slot.
        let current_slot = elapsed_ms / slot_ms;
        let next_slot_ms = (current_slot + 1) * slot_ms;

        genesis + Duration::from_millis(next_slot_ms)
    }
}

/// Compute the current slot for a given time, genesis, and slot duration.
/// Standalone function for testing without a tokio runtime.
#[cfg(test)]
fn compute_slot(now: SystemTime, genesis_time_unix: u64, slot_duration_ms: u64) -> u64 {
    let genesis = UNIX_EPOCH + Duration::from_secs(genesis_time_unix);
    let elapsed = now.duration_since(genesis).unwrap_or(Duration::ZERO);
    elapsed.as_millis() as u64 / slot_duration_ms
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn current_slot_computation() {
        // Genesis 100 seconds ago, 1-second slots.
        let now = SystemTime::now();
        let genesis_unix = now
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs()
            .saturating_sub(100);

        let slot = compute_slot(now, genesis_unix, 1000);
        // Should be approximately 100 (±1 for timing).
        assert!(slot >= 99 && slot <= 101, "slot was {slot}");
    }

    #[test]
    fn future_genesis_gives_slot_zero() {
        let future_unix = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs()
            + 3600;

        let slot = compute_slot(SystemTime::now(), future_unix, 1000);
        assert_eq!(slot, 0);
    }

    #[test]
    fn slot_at_exact_boundary() {
        let genesis = UNIX_EPOCH + Duration::from_secs(1000);
        // Exactly 10 seconds after genesis with 1-second slots.
        let at = genesis + Duration::from_secs(10);
        let slot = compute_slot(at, 1000, 1000);
        assert_eq!(slot, 10);
    }

    #[test]
    fn sub_second_slots() {
        let genesis = UNIX_EPOCH + Duration::from_secs(1000);
        // 5 seconds after genesis with 200ms slots = slot 25.
        let at = genesis + Duration::from_secs(5);
        let slot = compute_slot(at, 1000, 200);
        assert_eq!(slot, 25);
    }

    #[tokio::test]
    async fn tick_returns_current_slot() {
        // Genesis very recently, 100ms slots. The tick fires at the next
        // slot boundary, so the returned slot should be small but positive.
        let genesis_unix = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut clock = SlotClock::new(genesis_unix, 100);
        let slot = clock.tick().await;
        // First tick should be slot 1 (next boundary after genesis).
        // Allow up to 10 for CI/scheduling jitter (full workspace test
        // builds can take several seconds before reaching this point).
        assert!(slot >= 1 && slot <= 10, "slot was {slot}");
    }
}
