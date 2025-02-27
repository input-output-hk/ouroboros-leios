use std::{
    collections::{HashMap, VecDeque},
    hash::Hash,
    time::Duration,
};

use crate::clock::Timestamp;

struct MiniProtocolQueue<T> {
    queue: VecDeque<(T, u64)>,
}

impl<T> Default for MiniProtocolQueue<T> {
    fn default() -> Self {
        Self {
            queue: VecDeque::new(),
        }
    }
}

impl<T> MiniProtocolQueue<T> {
    fn push_back(&mut self, message: T, bytes: u64) {
        self.queue.push_back((message, bytes));
    }

    fn bytes(&self) -> u64 {
        self.queue.iter().map(|(_, bytes)| *bytes).sum()
    }

    fn bytes_in_next_message(&self) -> Option<u64> {
        self.queue.front().map(|(_, bytes)| *bytes)
    }

    fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn consume(&mut self, bytes: u64) -> impl Iterator<Item = (T, u64)> + use<'_, T> {
        let mut bytes_left = bytes;
        let mut end_index = 0;
        for (_, msg_left) in self.queue.iter_mut() {
            if *msg_left <= bytes_left {
                bytes_left -= *msg_left;
                end_index += 1;
            } else {
                *msg_left -= bytes_left;
                break;
            }
        }
        self.queue.drain(..end_index)
    }
}

pub struct Connection<TProtocol, TMessage> {
    bandwidth_bps: Option<u64>,
    latency: Duration,
    bandwidth_queues: HashMap<TProtocol, MiniProtocolQueue<(u64, TMessage)>>,
    latency_queue: VecDeque<(TMessage, Timestamp)>,
    last_event: Timestamp,
    next_id: u64,
}

impl<TProtocol, TMessage> Connection<TProtocol, TMessage>
where
    TProtocol: Eq + Hash,
{
    pub fn new(latency: Duration, bandwidth_bps: Option<u64>) -> Self {
        Self {
            bandwidth_bps,
            latency,
            bandwidth_queues: HashMap::new(),
            latency_queue: VecDeque::new(),
            last_event: Timestamp::zero(),
            next_id: 0,
        }
    }

    pub fn send(&mut self, message: TMessage, bytes: u64, miniprotocol: TProtocol, now: Timestamp) {
        if self.bandwidth_bps.is_none() {
            self.latency_queue.push_back((message, now + self.latency));
        } else {
            self.update_bandwidth_queues(now);
            self.bandwidth_queues
                .entry(miniprotocol)
                .or_default()
                .push_back((self.next_id, message), bytes);
            self.next_id += 1;
        }
    }

    pub fn next_arrival_time(&self) -> Option<Timestamp> {
        if let Some((_, timestamp)) = self.latency_queue.front() {
            return Some(*timestamp);
        }
        let bytes_left = self
            .bandwidth_queues
            .values()
            .filter_map(|q| q.bytes_in_next_message())
            .min()?;
        let bps = self.bandwidth_bps? / self.bandwidth_queues.len() as u64;
        Some(self.last_event + compute_bandwidth_delay(bps, bytes_left) + self.latency)
    }

    pub fn recv(&mut self, now: Timestamp) -> TMessage {
        self.update_bandwidth_queues(now);

        let (next_message, next_timestamp) = self
            .latency_queue
            .pop_front()
            .expect("Tried receiving too early");
        assert_eq!(next_timestamp, now);
        next_message
    }

    fn update_bandwidth_queues(&mut self, now: Timestamp) {
        let Some(total_bps) = self.bandwidth_bps else {
            return;
        };

        if self.last_event == now {
            return;
        }

        let mut bytes_to_consume =
            (now - self.last_event).as_micros() as u64 * total_bps / 1_000_000;

        let mut messages_received = vec![];
        while bytes_to_consume > 0 && !self.bandwidth_queues.is_empty() {
            let queues = self.bandwidth_queues.len() as u64;
            let bytes_per_queue = bytes_to_consume / queues;
            let bps = total_bps / queues;

            let bytes_to_consume_next = self
                .bandwidth_queues
                .values()
                .fold(bytes_per_queue, |bytes, queue| bytes.min(queue.bytes()));

            self.bandwidth_queues.retain(|_, queue| {
                let mut bytes_consumed = 0;
                for (message, size) in queue.consume(bytes_to_consume_next) {
                    bytes_consumed += size;
                    messages_received.push((
                        message,
                        self.last_event
                            + compute_bandwidth_delay(bps, bytes_consumed)
                            + self.latency,
                    ));
                }
                !queue.is_empty()
            });
            self.last_event += compute_bandwidth_delay(bps, bytes_to_consume_next);
            bytes_to_consume -= bytes_to_consume_next;
        }
        messages_received.sort_by_key(|((id, _), ts)| (*ts, *id));
        for ((_, message), arrival) in messages_received {
            self.latency_queue.push_back((message, arrival));
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

    #[derive(PartialEq, Eq, Hash)]
    enum MiniProtocol {
        One,
        Two,
    }

    #[test]
    fn should_return_messages_instantly_without_bandwidth_or_latency() {
        let latency = Duration::from_millis(0);
        let bandwidth_bps = None;
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 8, MiniProtocol::One, start);

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
        conn.send("message 1", 8, MiniProtocol::One, start);

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
        conn.send("message 1", 1000, MiniProtocol::One, start);

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
        conn.send("message 1", 1000, MiniProtocol::One, start);

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
        conn.send("message 1", 1000, MiniProtocol::One, start);
        conn.send("message 2", 1000, MiniProtocol::One, start);

        let first_arrival_time = start + Duration::from_secs(1);
        assert_eq!(conn.next_arrival_time(), Some(first_arrival_time));
        assert_eq!(conn.recv(first_arrival_time), "message 1");
        let second_arrival_time = first_arrival_time + Duration::from_secs(1);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(conn.recv(second_arrival_time), "message 2");
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_split_bandwidth_between_messages_over_different_miniprotocols() {
        let latency = Duration::ZERO;
        let bandwidth_bps = Some(1000);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 1000, MiniProtocol::One, start);
        conn.send("message 2", 1000, MiniProtocol::Two, start);

        let arrival_time = start + Duration::from_secs(2);
        assert_eq!(conn.next_arrival_time(), Some(arrival_time));
        assert_eq!(conn.recv(arrival_time), "message 1");
        assert_eq!(conn.next_arrival_time(), Some(arrival_time));
        assert_eq!(conn.recv(arrival_time), "message 2");
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
        conn.send("message 1", 1000, MiniProtocol::One, start);
        assert_eq!(conn.next_arrival_time(), Some(first_arrival_time));

        let second_start = start + Duration::from_millis(500);
        conn.send("message 2", 1000, MiniProtocol::One, second_start);

        assert_eq!(conn.next_arrival_time(), Some(first_arrival_time));
        assert_eq!(conn.recv(first_arrival_time), "message 1");
        let second_arrival_time = first_arrival_time + Duration::from_millis(1000);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(conn.recv(second_arrival_time), "message 2");
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_stop_splitting_bandwidth_when_one_message_goes_through() {
        let latency = Duration::ZERO;
        let bandwidth_bps = Some(1000);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 1000, MiniProtocol::One, start);
        conn.send("message 2", 2000, MiniProtocol::Two, start);

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
        conn.send("message 1", 1000, MiniProtocol::One, start);
        assert_eq!(conn.next_arrival_time(), Some(og_first_arrival_time));

        let second_start = start + Duration::from_millis(500);
        conn.send("message 2", 1000, MiniProtocol::Two, second_start);

        let first_arrival_time = start + Duration::from_millis(1500);
        assert_eq!(conn.next_arrival_time(), Some(first_arrival_time));
        assert_eq!(conn.recv(first_arrival_time), "message 1");
        let second_arrival_time = first_arrival_time + Duration::from_millis(500);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(conn.recv(second_arrival_time), "message 2");
        assert_eq!(conn.next_arrival_time(), None);
    }
}
