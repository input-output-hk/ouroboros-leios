use std::{
    cell::Cell,
    collections::{BinaryHeap, VecDeque},
    time::Duration,
};

use crate::clock::Timestamp;

pub struct Connection<T> {
    bandwidth_bps: Option<u64>,
    latency: Duration,
    // the messages with the fewest bytes left will be received sooner
    bandwidth_queue: BinaryHeap<Envelope<T>>,
    // every message has the same latency, so this is FIFO
    latency_queue: VecDeque<(T, Timestamp)>,
    next_id: u64,
    last_event: Timestamp,
}

impl<T> Connection<T> {
    pub fn new(latency: Duration, bandwidth_bps: Option<u64>) -> Self {
        Self {
            bandwidth_bps,
            latency,
            bandwidth_queue: BinaryHeap::new(),
            latency_queue: VecDeque::new(),
            next_id: 0,
            last_event: Timestamp::zero(),
        }
    }

    pub fn send(&mut self, message: T, bytes: u64, now: Timestamp) {
        if self.bandwidth_bps.is_none() {
            self.latency_queue.push_back((message, now + self.latency));
        } else {
            self.update_bandwidth_queue(now);
            let id = self.next_id;
            self.next_id += 1;
            self.bandwidth_queue.push(Envelope {
                id,
                body: message,
                bytes_left: Cell::new(bytes),
            });
        }
    }

    pub fn next_arrival_time(&self) -> Option<Timestamp> {
        if let Some((_, timestamp)) = self.latency_queue.front() {
            return Some(*timestamp);
        }
        let next_bandwidther = self.bandwidth_queue.peek()?;
        let bps = self.bandwidth_bps? / self.bandwidth_queue.len() as u64;
        Some(
            self.last_event
                + compute_bandwidth_delay(bps, next_bandwidther.bytes_left.get())
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
        let Some(total_bandwidth) = self.bandwidth_bps else {
            return;
        };

        if self.last_event == now {
            return;
        }

        let mut bytes_consumed = 0;
        while let Some(envelope) = self.bandwidth_queue.peek() {
            let bps = total_bandwidth / self.bandwidth_queue.len() as u64;
            let next_event = self.last_event
                + compute_bandwidth_delay(bps, envelope.bytes_left.get() - bytes_consumed);
            if next_event <= now {
                let envelope = self.bandwidth_queue.pop().unwrap();
                bytes_consumed = envelope.bytes_left.get();
                let arrival_time = next_event + self.latency;
                self.latency_queue.push_back((envelope.body, arrival_time));
                self.last_event = next_event;
            } else {
                let elapsed = now - self.last_event;
                bytes_consumed += elapsed.as_micros() as u64 * bps / 1_000_000;
                break;
            }
        }

        self.last_event = now;

        // update how many bytes are left for remaining queue items
        // this updates every item by the same amount,
        // so it doesn't violate BinaryHeap invariants.
        if bytes_consumed == 0 {
            return;
        }
        for envelope in self.bandwidth_queue.iter() {
            let bytes_left = envelope.bytes_left.get();
            envelope.bytes_left.set(bytes_left - bytes_consumed);
        }
    }
}

fn compute_bandwidth_delay(bps: u64, bytes: u64) -> Duration {
    Duration::from_micros((bytes * 1_000_000) / bps)
}

// Ordering is by fewest bytes left, then by lowest id.
struct Envelope<T> {
    id: u64,
    body: T,
    bytes_left: Cell<u64>,
}

impl<T> PartialEq for Envelope<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id.eq(&other.id)
    }
}
impl<T> Eq for Envelope<T> {}

impl<T> PartialOrd for Envelope<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<T> Ord for Envelope<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.bytes_left
            .cmp(&other.bytes_left)
            .then(self.id.cmp(&other.id))
            .reverse()
    }
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
    fn should_split_bandwidth_between_scheduled_messages() {
        let latency = Duration::ZERO;
        let bandwidth_bps = Some(1000);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 1000, start);
        conn.send("message 2", 1000, start);

        let arrival_time = start + Duration::from_secs(2);
        assert_eq!(conn.next_arrival_time(), Some(arrival_time));
        assert_eq!(conn.recv(arrival_time), "message 1");
        assert_eq!(conn.next_arrival_time(), Some(arrival_time));
        assert_eq!(conn.recv(arrival_time), "message 2");
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_stop_splitting_bandwidth_when_one_message_goes_through() {
        let latency = Duration::ZERO;
        let bandwidth_bps = Some(1000);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 1000, start);
        conn.send("message 2", 2000, start);

        let first_arrival_time = start + Duration::from_secs(2);
        assert_eq!(conn.next_arrival_time(), Some(first_arrival_time));
        assert_eq!(conn.recv(first_arrival_time), "message 1");
        let second_arrival_time = first_arrival_time + Duration::from_secs(1);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(conn.recv(second_arrival_time), "message 2");
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_start_splitting_bandwidth_when_second_message_is_sent() {
        let latency = Duration::ZERO;
        let bandwidth_bps = Some(1000);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        let og_first_arrival_time = start + Duration::from_secs(1);
        conn.send("message 1", 1000, start);
        assert_eq!(conn.next_arrival_time(), Some(og_first_arrival_time));

        let second_start = start + Duration::from_millis(500);
        conn.send("message 2", 1000, second_start);

        let first_arrival_time = start + Duration::from_millis(1500);
        assert_eq!(conn.next_arrival_time(), Some(first_arrival_time));
        assert_eq!(conn.recv(first_arrival_time), "message 1");
        let second_arrival_time = first_arrival_time + Duration::from_millis(500);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(conn.recv(second_arrival_time), "message 2");
        assert_eq!(conn.next_arrival_time(), None);
    }
}
