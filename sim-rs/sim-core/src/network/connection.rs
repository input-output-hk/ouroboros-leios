use std::{
    collections::{BTreeMap, VecDeque},
    time::Duration,
};

use tcp_model::{LinkEnvelopeCfg, LinkState};

use crate::{clock::Timestamp, config::NodeId, rng::Rng, tcp::TcpConnProps};

use super::tcp_connection::{DEFAULT_TCP_BANDWIDTH, TcpConnection};

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
    // BTreeMap (not HashMap) so that split_bytes_amongst_queues iterates in a
    // deterministic order. The +1-byte remainder distribution below is
    // sensitive to tie-breaks between equal-sized queues; using a HashMap
    // leaks std RandomState hashing into simulation state. Do not change.
    bandwidth_queues: BTreeMap<TProtocol, MiniProtocolQueue<(u64, TMessage)>>,
    latency_queue: VecDeque<(TMessage, Timestamp)>,
    last_event: Timestamp,
    next_id: u64,
    envelope: Option<EnvelopeWiring>,
}

/// Per-link state for the analytic TCP envelope model plus the deterministic
/// oracle and link identity used to seed loss draws.
pub struct EnvelopeWiring {
    pub state: LinkState,
    pub rng: Rng,
    pub from: NodeId,
    pub to: NodeId,
}

impl EnvelopeWiring {
    pub fn new(cfg: LinkEnvelopeCfg, rng: Rng, from: NodeId, to: NodeId) -> Self {
        Self {
            state: LinkState::new(cfg),
            rng,
            from,
            to,
        }
    }
}

impl<TProtocol, TMessage> Connection<TProtocol, TMessage>
where
    TProtocol: Clone + Ord,
{
    pub fn new(latency: Duration, bandwidth_bps: Option<u64>) -> Self {
        Self::new_inner(latency, bandwidth_bps, None)
    }

    /// Constructor that attaches a [`tcp_model::LinkState`] driving slow-start,
    /// idle-reset, and per-message loss for this directed link. Behaviour
    /// matches [`Self::new`] exactly when the cfg is [`LinkEnvelopeCfg::disabled`].
    pub fn with_envelope(
        latency: Duration,
        bandwidth_bps: Option<u64>,
        envelope: EnvelopeWiring,
    ) -> Self {
        Self::new_inner(latency, bandwidth_bps, Some(envelope))
    }

    fn new_inner(
        latency: Duration,
        bandwidth_bps: Option<u64>,
        envelope: Option<EnvelopeWiring>,
    ) -> Self {
        Self {
            bandwidth_bps,
            latency,
            bandwidth_queues: BTreeMap::new(),
            latency_queue: VecDeque::new(),
            last_event: Timestamp::zero(),
            next_id: 0,
            envelope,
        }
    }

    /// Absolute time below which arrivals are not delivered, given the current
    /// envelope state. `t` is returned unchanged when no stall is active or no
    /// envelope is attached.
    fn delivery_floor(&self, t: Timestamp) -> Timestamp {
        let Some(env) = &self.envelope else { return t };
        let floor_dur = env.state.delivery_floor(t - Timestamp::zero());
        Timestamp::zero() + floor_dur
    }

    /// Fires the cold/idle envelope and the per-message loss draw for the
    /// pending message. The loss outcome is deterministic in
    /// `(global_seed, from, to, send_time_nanos, message_id)`.
    fn run_on_send(&mut self, bytes: u64, now: Timestamp) {
        let Some(env) = self.envelope.as_mut() else {
            return;
        };
        let send_dur = now - Timestamp::zero();
        let p = env.state.cfg().msg_loss_prob(bytes);
        let loss = p > 0.0
            && env.rng.draw_bool_with_context(
                &("tcp_loss", env.from, env.to, send_dur, self.next_id),
                p,
            );
        env.state.on_send(send_dur, bytes, loss);
    }

    /// Returns (message_count, total_bytes) across all bandwidth and latency queues.
    pub fn queue_stats(&self) -> (usize, u64) {
        let mut count = 0usize;
        let mut bytes = 0u64;
        for q in self.bandwidth_queues.values() {
            count += q.queue.len();
            bytes += q.bytes();
        }
        count += self.latency_queue.len();
        // latency_queue doesn't track bytes, estimate from count
        (count, bytes)
    }

    pub fn send(&mut self, message: TMessage, bytes: u64, miniprotocol: TProtocol, now: Timestamp) {
        if self.bandwidth_bps.is_none() {
            self.run_on_send(bytes, now);
            let arrival = self.delivery_floor(now + self.latency);
            self.latency_queue.push_back((message, arrival));
        } else {
            self.update_bandwidth_queues(now);
            self.run_on_send(bytes, now);
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
        let raw = self.last_event
            + compute_bandwidth_delay(
                self.bandwidth_bps?,
                self.bandwidth_queues.len() as u64,
                bytes_left,
            )
            + self.latency;
        Some(self.delivery_floor(raw))
    }

    pub fn recv_many(&mut self, now: Timestamp) -> Vec<(TMessage, Timestamp)> {
        self.update_bandwidth_queues(now);
        let mut results = vec![];
        while self.latency_queue.front().is_some_and(|(_, t)| t <= &now) {
            results.push(self.latency_queue.pop_front().unwrap());
        }
        results
    }

    fn update_bandwidth_queues(&mut self, now: Timestamp) {
        let Some(total_bps) = self.bandwidth_bps else {
            return;
        };

        if self.last_event == now {
            return;
        }

        // Total bytes the link could push over [last_event, now]. With no
        // envelope this is `bps * elapsed`; with an envelope it integrates
        // `bps * bw_mult(s)` so that slow-start, idle reset and loss-stall
        // bandwidth dips are honoured.
        let mut bytes_to_consume = match &self.envelope {
            Some(env) => env.state.bytes_deliverable(
                total_bps,
                self.last_event - Timestamp::zero(),
                now - Timestamp::zero(),
            ),
            None => (now - self.last_event).as_micros() as u64 * total_bps / 1_000_000,
        };

        let mut messages_received = vec![];
        while bytes_to_consume > 0 && !self.bandwidth_queues.is_empty() {
            let queues = self.bandwidth_queues.len() as u64;
            let bytes_per_queue = self.split_bytes_amongst_queues(bytes_to_consume);
            let total_bytes_consumed: u64 = bytes_per_queue.values().copied().sum();

            let envelope = self.envelope.as_ref();
            let latency = self.latency;
            let round_t0 = self.last_event;
            let envelope_active = envelope.is_some_and(|e| e.state.has_active_envelopes());
            let arrival_after = |link_bytes: u64| -> Timestamp {
                if !envelope_active {
                    return round_t0 + compute_bandwidth_delay(total_bps, 1, link_bytes) + latency;
                }
                let env = envelope.unwrap();
                let t = env.state.invert_bytes_deliverable(
                    total_bps,
                    link_bytes,
                    round_t0 - Timestamp::zero(),
                    now - Timestamp::zero(),
                );
                Timestamp::zero() + t + latency
            };

            self.bandwidth_queues.retain(|key, queue| {
                let mut bytes_consumed = 0;
                let Some(&bytes_to_consume_next) = bytes_per_queue.get(key) else {
                    return true;
                };
                for (message, size) in queue.consume(bytes_to_consume_next) {
                    bytes_consumed += size;
                    messages_received.push((message, arrival_after(bytes_consumed * queues)));
                }
                bytes_to_consume -= bytes_to_consume_next;
                !queue.is_empty()
            });
            // Advance last_event by the time taken to consume the whole pool
            // (so the next iteration of this loop sees the correct t0).
            self.last_event = arrival_after(total_bytes_consumed) - self.latency;
        }
        messages_received.sort_by_key(|((id, _), ts)| (*ts, *id));
        for ((_, message), arrival) in messages_received {
            let clamped = self.delivery_floor(arrival);
            self.latency_queue.push_back((message, clamped));
        }

        self.last_event = now;
    }


    fn split_bytes_amongst_queues(&self, bytes: u64) -> BTreeMap<TProtocol, u64> {
        let mut queue_bytes: Vec<(&TProtocol, u64)> = self
            .bandwidth_queues
            .iter()
            .map(|(k, v)| (k, v.bytes()))
            .collect();
        // Stable sort by bytes; BTreeMap::iter yields keys in ascending order,
        // so ties break deterministically by TProtocol's Ord.
        queue_bytes.sort_by_key(|(_, bytes)| *bytes);
        let queues = queue_bytes.len() as u64;
        let target_bytes_per_queue = bytes / queues;
        let bytes_per_queue = target_bytes_per_queue.min(queue_bytes[0].1);
        if bytes_per_queue == target_bytes_per_queue {
            let mut bytes_left = bytes % queues;
            for (_, bytes) in queue_bytes.iter_mut() {
                if bytes_left > 0 && *bytes > bytes_per_queue {
                    bytes_left -= 1;
                    *bytes = bytes_per_queue + 1;
                } else {
                    *bytes = bytes_per_queue;
                }
            }
        } else {
            for (_, bytes) in queue_bytes.iter_mut() {
                *bytes = bytes_per_queue;
            }
        }
        queue_bytes
            .into_iter()
            .filter_map(|(k, v)| (v > 0).then_some((k.clone(), v)))
            .collect()
    }
}

fn compute_bandwidth_delay(total_bps: u64, split: u64, bytes: u64) -> Duration {
    Duration::from_micros((bytes * 1_000_000) * split / total_bps)
}

#[cfg(test)]
#[allow(clippy::items_after_test_module)]
mod tests {
    use std::time::Duration;

    use crate::clock::Timestamp;

    use super::Connection;

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
    enum MiniProtocol {
        One,
        Two,
        Three,
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
        assert_eq!(conn.recv_many(start), vec![("message 1", start)]);
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
        assert_eq!(
            conn.recv_many(arrival_time),
            vec![("message 1", arrival_time)]
        );
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
        assert_eq!(
            conn.recv_many(arrival_time),
            vec![("message 1", arrival_time)]
        );
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
        assert_eq!(
            conn.recv_many(arrival_time),
            vec![("message 1", arrival_time)]
        );
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
        assert_eq!(
            conn.recv_many(first_arrival_time),
            vec![("message 1", first_arrival_time)]
        );
        let second_arrival_time = first_arrival_time + Duration::from_secs(1);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(
            conn.recv_many(second_arrival_time),
            vec![("message 2", second_arrival_time)]
        );
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
        assert_eq!(
            conn.recv_many(arrival_time),
            vec![("message 1", arrival_time), ("message 2", arrival_time)]
        );
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_use_all_available_bandwidth() {
        let latency = Duration::ZERO;
        let bandwidth_bps = Some(4);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 10, MiniProtocol::One, start);
        conn.send("message 2", 10, MiniProtocol::Two, start);
        conn.send("message 3", 10, MiniProtocol::Three, start);

        let arrival_time = start + Duration::from_secs_f32(7.5);
        assert_eq!(conn.next_arrival_time(), Some(arrival_time));
        assert_eq!(
            conn.recv_many(arrival_time),
            vec![
                ("message 1", arrival_time),
                ("message 2", arrival_time),
                ("message 3", arrival_time)
            ]
        );
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
        assert_eq!(
            conn.recv_many(first_arrival_time),
            vec![("message 1", first_arrival_time)]
        );
        let second_arrival_time = first_arrival_time + Duration::from_millis(1000);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(
            conn.recv_many(second_arrival_time),
            vec![("message 2", second_arrival_time)]
        );
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
        assert_eq!(
            conn.recv_many(first_arrival_time),
            vec![("message 1", first_arrival_time)]
        );
        let second_arrival_time = first_arrival_time + Duration::from_secs(1);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(
            conn.recv_many(second_arrival_time),
            vec![("message 2", second_arrival_time)]
        );
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_split_bandwidth_correctly_when_multiple_miniprotocols_complete_at_once() {
        let latency = Duration::ZERO;
        let bandwidth_bps = Some(1000);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 1000, MiniProtocol::One, start);
        conn.send("message 2", 1000, MiniProtocol::Two, start);
        conn.send("message 3", 2000, MiniProtocol::Three, start);

        let first_arrival_time = start + Duration::from_secs(3);
        assert_eq!(
            conn.recv_many(first_arrival_time),
            vec![
                ("message 1", first_arrival_time),
                ("message 2", first_arrival_time),
            ]
        );
        let second_arrival_time = first_arrival_time + Duration::from_secs(1);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(
            conn.recv_many(second_arrival_time),
            vec![("message 3", second_arrival_time)],
        );
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
        assert_eq!(
            conn.recv_many(first_arrival_time),
            vec![("message 1", first_arrival_time)],
        );
        let second_arrival_time = first_arrival_time + Duration::from_millis(500);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(
            conn.recv_many(second_arrival_time),
            vec![("message 2", second_arrival_time)],
        );
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_split_bandwidth_correctly_under_high_latency() {
        let latency = Duration::from_millis(1000);
        let bandwidth_bps = Some(900);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 300, MiniProtocol::One, start);
        conn.send("message 2", 300, MiniProtocol::Two, start);
        conn.send("message 3", 1200, MiniProtocol::Three, start);

        let first_arrival_time = start + Duration::from_secs(2);
        assert_eq!(conn.next_arrival_time(), Some(first_arrival_time));
        assert_eq!(
            conn.recv_many(first_arrival_time),
            vec![
                ("message 1", first_arrival_time),
                ("message 2", first_arrival_time),
            ],
        );
        let second_arrival_time = first_arrival_time + Duration::from_secs(1);
        assert_eq!(conn.next_arrival_time(), Some(second_arrival_time));
        assert_eq!(
            conn.recv_many(second_arrival_time),
            vec![("message 3", second_arrival_time)],
        );
        assert_eq!(conn.next_arrival_time(), None);
    }

    #[test]
    fn should_accept_timestamps_from_later_than_next_event() {
        let latency = Duration::ZERO;
        let bandwidth_bps = Some(4);
        let mut conn = Connection::new(latency, bandwidth_bps);
        assert_eq!(conn.next_arrival_time(), None);

        let start = Timestamp::zero() + Duration::from_secs(1);
        conn.send("message 1", 10, MiniProtocol::One, start);
        conn.send("message 2", 10, MiniProtocol::Two, start);
        conn.send("message 3", 10, MiniProtocol::Three, start);

        let arrival_time = start + Duration::from_secs_f32(7.5);
        let future_arrival_time = start + Duration::from_secs(10);

        assert_eq!(conn.next_arrival_time(), Some(arrival_time));
        assert_eq!(
            conn.recv_many(future_arrival_time),
            vec![
                ("message 1", arrival_time),
                ("message 2", arrival_time),
                ("message 3", arrival_time),
            ],
        );
        assert_eq!(conn.next_arrival_time(), None);
    }

    fn envelope_for(latency: Duration, bps: u64, loss_p: f64) -> super::EnvelopeWiring {
        use crate::config::NodeId;
        use tcp_model::LinkEnvelopeCfg;
        let mut cfg = LinkEnvelopeCfg::defaults_for(latency, bps);
        cfg.loss_prob_per_segment = loss_p;
        super::EnvelopeWiring::new(cfg, crate::rng::Rng::new(0xC0FFEE), NodeId::new(1), NodeId::new(2))
    }

    #[test]
    fn envelope_slow_start_delays_cold_message_vs_no_envelope() {
        let latency = Duration::from_millis(150);
        let bps = 1_000_000u64;
        let far_future = Timestamp::zero() + Duration::from_secs(20);

        let mut warm = Connection::<MiniProtocol, &'static str>::new(latency, Some(bps));
        warm.send("m", 1_000_000, MiniProtocol::One, Timestamp::zero());
        let warm_arrival = warm.recv_many(far_future)[0].1;

        let mut cold = Connection::with_envelope(latency, Some(bps), envelope_for(latency, bps, 0.0));
        cold.send("m", 1_000_000, MiniProtocol::One, Timestamp::zero());
        let cold_arrival = cold.recv_many(far_future)[0].1;

        // Warm pipe: 1MB / 1MB/s + 150ms ≈ 1.15s. Cold pipe: slow-start ramp
        // pushes it noticeably later.
        assert!(
            cold_arrival > warm_arrival + Duration::from_millis(500),
            "cold {cold_arrival:?} vs warm {warm_arrival:?} delta too small"
        );
    }

    #[test]
    fn envelope_loss_pushes_arrival_to_delivery_floor() {
        let latency = Duration::from_millis(150);
        let bps = 1_000_000u64;
        let mut conn = Connection::with_envelope(latency, Some(bps), envelope_for(latency, bps, 1.0));
        let send_at = Timestamp::zero() + Duration::from_millis(100);
        conn.send("m", 1500, MiniProtocol::One, send_at);
        let arrival = conn.recv_many(send_at + Duration::from_secs(5))[0].1;
        // Loss certain → stall window = RTO = max(1s, 2*latency) = 1s.
        let floor = send_at + Duration::from_secs(1);
        assert!(arrival >= floor, "arrival {arrival:?} below floor {floor:?}");
    }

    #[test]
    fn envelope_disabled_matches_no_envelope_byte_for_byte() {
        use tcp_model::LinkEnvelopeCfg;
        let latency = Duration::from_millis(10);
        let bps = 1_000u64;

        let mut plain = Connection::<MiniProtocol, &'static str>::new(latency, Some(bps));
        let wiring = super::EnvelopeWiring::new(
            LinkEnvelopeCfg::disabled(),
            crate::rng::Rng::new(0),
            crate::config::NodeId::new(1),
            crate::config::NodeId::new(2),
        );
        let mut env = Connection::with_envelope(latency, Some(bps), wiring);

        let start = Timestamp::zero() + Duration::from_secs(1);
        for (i, p) in [MiniProtocol::One, MiniProtocol::Two, MiniProtocol::Three].into_iter().enumerate() {
            let when = start + Duration::from_millis(50 * i as u64);
            plain.send("m", 100, p.clone(), when);
            env.send("m", 100, p, when);
        }
        let later = start + Duration::from_secs(5);
        let plain_msgs = plain.recv_many(later);
        let env_msgs = env.recv_many(later);
        assert_eq!(plain_msgs.len(), env_msgs.len());
        for ((pm, pt), (em, et)) in plain_msgs.iter().zip(env_msgs.iter()) {
            assert_eq!(pm, em);
            assert_eq!(pt, et, "envelope-disabled arrival diverged from baseline");
        }
    }
}

// ── Connection kind ───────────────────────────────────────────────────────────

/// Either a bandwidth-sharing connection or a TCP congestion-window connection.
///
/// Both present the same interface so the rest of the network layer can treat
/// them uniformly.
#[allow(clippy::large_enum_variant)]
pub enum ConnectionKind<TProtocol, TMessage> {
    /// Fair-bandwidth-sharing model (the existing `Connection`).
    Simple(Connection<TProtocol, TMessage>),
    /// TCP congestion-window model (`TcpConnection`).  The `TProtocol` tag is
    /// accepted for API compatibility but ignored — all protocols share the
    /// single TCP stream, matching real TCP mux behaviour.
    Tcp(TcpConnection<TMessage>),
}

impl<TProtocol: Clone + Ord, TMessage> ConnectionKind<TProtocol, TMessage> {
    pub fn simple(latency: Duration, bandwidth_bps: Option<u64>) -> Self {
        Self::Simple(Connection::new(latency, bandwidth_bps))
    }

    pub fn tcp(latency: Duration, bandwidth_bps: Option<u64>) -> Self {
        let bandwidth = bandwidth_bps.unwrap_or(DEFAULT_TCP_BANDWIDTH);
        Self::Tcp(TcpConnection::new(TcpConnProps::new(latency, bandwidth)))
    }

    pub fn from_config(
        latency: Duration,
        bandwidth_bps: Option<u64>,
        use_tcp: bool,
        envelope: Option<EnvelopeWiring>,
    ) -> Self {
        if use_tcp {
            debug_assert!(
                envelope.is_none(),
                "use-tcp and tcp-envelope are mutually exclusive; tcp-envelope ignored",
            );
            Self::tcp(latency, bandwidth_bps)
        } else {
            match envelope {
                Some(wiring) => Self::Simple(Connection::with_envelope(
                    latency,
                    bandwidth_bps,
                    wiring,
                )),
                None => Self::simple(latency, bandwidth_bps),
            }
        }
    }

    pub fn send(
        &mut self,
        message: TMessage,
        bytes: u64,
        protocol: TProtocol,
        now: Timestamp,
    ) {
        match self {
            Self::Simple(c) => c.send(message, bytes, protocol, now),
            Self::Tcp(c) => c.send(message, bytes, now),
        }
    }

    pub fn next_arrival_time(&self) -> Option<Timestamp> {
        match self {
            Self::Simple(c) => c.next_arrival_time(),
            Self::Tcp(c) => c.next_arrival_time(),
        }
    }

    pub fn recv_many(&mut self, now: Timestamp) -> Vec<(TMessage, Timestamp)> {
        match self {
            Self::Simple(c) => c.recv_many(now),
            Self::Tcp(c) => c.recv_many(now),
        }
    }

    pub fn queue_stats(&self) -> (usize, u64) {
        match self {
            Self::Simple(c) => c.queue_stats(),
            Self::Tcp(c) => c.queue_stats(),
        }
    }
}
