use std::{collections::VecDeque, time::Duration};

use crate::clock::Timestamp;

pub struct Connection<T> {
    bandwidth_bps: Option<u64>,
    latency: Duration,
    // messages go across the channel one-at-a-time, so this is FIFO
    bandwidth_queue: VecDeque<(T, u64)>,
    // every message has the same latency, so this is FIFO
    latency_queue: VecDeque<(T, Timestamp)>,
    last_event: Timestamp,
}

impl<T> Connection<T> {
    pub fn new(latency: Duration, bandwidth_bps: Option<u64>) -> Self {
        Self {
            bandwidth_bps,
            latency,
            bandwidth_queue: VecDeque::new(),
            latency_queue: VecDeque::new(),
            last_event: Timestamp::zero(),
        }
    }

    pub fn send(&mut self, message: T, bytes: u64, now: Timestamp) {
        if self.bandwidth_bps.is_none() {
            self.latency_queue.push_back((message, now + self.latency));
        } else {
            self.update_bandwidth_queue(now);
            self.bandwidth_queue.push_back((message, bytes));
        }
    }

    pub fn next_arrival_time(&self) -> Option<Timestamp> {
        if let Some((_, timestamp)) = self.latency_queue.front() {
            return Some(*timestamp);
        }
        let (_, bytes_left) = self.bandwidth_queue.front()?;
        Some(
            self.last_event
                + compute_bandwidth_delay(self.bandwidth_bps?, *bytes_left)
                + self.latency,
        )
    }

    pub fn recv(&mut self, now: Timestamp) -> T {
        self.update_bandwidth_queue(now);

        let (next_message, next_timestamp) = self
            .latency_queue
            .pop_front()
            .expect("Tried receiving too early");
        assert_eq!(next_timestamp, now);
        next_message
    }

    fn update_bandwidth_queue(&mut self, now: Timestamp) {
        let Some(bps) = self.bandwidth_bps else {
            return;
        };

        if self.last_event == now {
            return;
        }

        while let Some((_, bytes)) = self.bandwidth_queue.front_mut() {
            let next_event = self.last_event + compute_bandwidth_delay(bps, *bytes);
            if next_event <= now {
                let (message, _) = self.bandwidth_queue.pop_front().unwrap();
                let arrival_time = next_event + self.latency;
                self.latency_queue.push_back((message, arrival_time));
                self.last_event = next_event;
            } else {
                let elapsed = now - self.last_event;
                *bytes -= elapsed.as_micros() as u64 * bps / 1_000_000;
                break;
            }
        }

        self.last_event = now;
    }
}

fn compute_bandwidth_delay(bps: u64, bytes: u64) -> Duration {
    Duration::from_micros((bytes * 1_000_000) / bps)
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::clock::Timestamp;

    use super::Connection;

    #[test]
    fn should_return_messages_instantly_without_bandwidth_or_latency() {
        let latency = Duration::from_millis(0);
        let bandwidth_bps = None;
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 8, start);

        assert_eq!(conn.next_arrival_time(), Some(start));
        assert_eq!(conn.recv(start), "message 1");
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_respect_latency() {
        let latency = Duration::from_millis(10);
        let bandwidth_bps = None;
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 8, start);

        let arrival_time = start + latency;
        assert_eq!(conn.next_arrival_time(), Some(arrival_time));
        assert_eq!(conn.recv(arrival_time), "message 1");
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_respect_bandwidth() {
        let latency = Duration::ZERO;
        let bandwidth_bps = Some(1000);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 1000, start);

        let arrival_time = start + Duration::from_secs(1);
        assert_eq!(conn.next_arrival_time(), Some(arrival_time));
        assert_eq!(conn.recv(arrival_time), "message 1");
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_respect_both_bandwidth_and_latency() {
        let latency = Duration::from_millis(1337);
        let bandwidth_bps = Some(1000);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 1000, start);

        let arrival_time = start + Duration::from_millis(2337);
        assert_eq!(conn.next_arrival_time(), Some(arrival_time));
        assert_eq!(conn.recv(arrival_time), "message 1");
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_use_all_bandwidth_for_one_message_at_a_time() {
        let latency = Duration::ZERO;
        let bandwidth_bps = Some(1000);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 1000, start);
        conn.send("message 2", 1000, start);

        let first_arrival_time = start + Duration::from_secs(1);
        assert_eq!(conn.next_arrival_time(), Some(first_arrival_time));
        assert_eq!(conn.recv(first_arrival_time), "message 1");
        let second_arrival_time = first_arrival_time + Duration::from_secs(1);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(conn.recv(second_arrival_time), "message 2");
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_delay_second_message_if_first_one_is_in_flight() {
        let latency = Duration::ZERO;
        let bandwidth_bps = Some(1000);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        let first_arrival_time = start + Duration::from_secs(1);
        conn.send("message 1", 1000, start);
        assert_eq!(conn.next_arrival_time(), Some(first_arrival_time));

        let second_start = start + Duration::from_millis(500);
        conn.send("message 2", 1000, second_start);

        assert_eq!(conn.next_arrival_time(), Some(first_arrival_time));
        assert_eq!(conn.recv(first_arrival_time), "message 1");
        let second_arrival_time = first_arrival_time + Duration::from_millis(1000);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(conn.recv(second_arrival_time), "message 2");
        assert_eq!(conn.next_arrival_time(), None);
    }
}
