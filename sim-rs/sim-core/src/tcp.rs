//! TCP congestion-window model.
//!
//! A direct port of the Haskell `simulation/src/ModelTCP.hs` module.
//!
//! The model forecasts send timing for a stream of messages over a single TCP
//! connection, accounting for serialisation delay, one-way propagation latency,
//! and the congestion window.  It does *not* model loss, retransmission, or
//! delayed ACKs; those are out of scope for the simulation's fidelity target.
//!
//! ## Key approximation ("strategic cheat")
//!
//! ACK timestamps are anchored to the *receive leading edge*, not the trailing
//! edge (see [`do_send`]).  In real TCP, per-segment ACKs start arriving one
//! RTT after the sender begins transmitting; using the trailing edge instead
//! would defer every window refill by one extra serialisation period, making
//! the model systematically understate throughput when the congestion window is
//! large relative to the bandwidth-delay product.

use std::{cmp::Reverse, collections::BinaryHeap, time::Duration};

use crate::clock::Timestamp;

// ── Connection properties ────────────────────────────────────────────────────

/// Fixed characteristics of a TCP link.
#[derive(Debug, Clone)]
pub struct TcpConnProps {
    /// One-way propagation latency.
    pub latency: Duration,
    /// Sender serialisation rate (bytes per second).
    pub bandwidth: u64,
    /// Receiver window: hard cap on the congestion window size.
    pub receiver_window: u64,
}

impl TcpConnProps {
    /// Construct `TcpConnProps`, auto-sizing the receiver window to at least
    /// 2 × the bandwidth–delay product so it never constrains throughput.
    pub fn new(latency: Duration, bandwidth: u64) -> Self {
        let bdp2 = (bandwidth as f64 * latency.as_secs_f64() * 2.0).ceil() as u64;
        Self {
            latency,
            bandwidth,
            receiver_window: bdp2.max(10 * SEGMENT_SIZE),
        }
    }
}

/// Canonical TCP maximum segment size (bytes).
pub const SEGMENT_SIZE: u64 = 1460;

/// Modern TCP initial congestion window: 10 segments (RFC 6928).
const INITIAL_CONGESTION_WINDOW: u64 = 10 * SEGMENT_SIZE;

// ── State ────────────────────────────────────────────────────────────────────

/// Per-connection mutable sender state.
pub struct TcpState {
    congestion_window: u64,
    available_congestion_window: u64,
    /// Min-heap of pending ACKs: `(arrival_time, bytes_freed)`.
    acknowledgements: BinaryHeap<Reverse<(Timestamp, u64)>>,
}

impl Default for TcpState {
    fn default() -> Self {
        Self {
            congestion_window: INITIAL_CONGESTION_WINDOW,
            available_congestion_window: INITIAL_CONGESTION_WINDOW,
            acknowledgements: BinaryHeap::new(),
        }
    }
}

impl TcpState {
    /// Returns true iff every scheduled ACK has already arrived by `now`.
    /// Used by `TcpConnection` to decide whether the idle-reset condition holds.
    pub fn all_acks_arrived(&self, now: Timestamp) -> bool {
        self.acknowledgements
            .iter()
            .all(|Reverse((ts, _))| *ts <= now)
    }
}

// ── Forecast ─────────────────────────────────────────────────────────────────

/// Timing forecast for one message or fragment.
#[derive(Debug, Clone)]
pub struct TcpMsgForecast {
    /// Sender starts transmitting.
    pub send_leading_edge: Timestamp,
    /// Sender finishes transmitting.
    pub send_trailing_edge: Timestamp,
    /// First byte arrives at receiver.
    pub recv_leading_edge: Timestamp,
    /// Last byte arrives at receiver.
    pub recv_trailing_edge: Timestamp,
    /// Last ACK returns to sender.
    pub acknowledgement: Timestamp,
    pub size: u64,
}

/// A complete TCP send event: overall timing plus per-fragment breakdown.
pub struct TcpEvent<M> {
    pub msg: M,
    pub overall: TcpMsgForecast,
    pub fragments: Vec<TcpMsgForecast>,
}

// ── Core algorithm ───────────────────────────────────────────────────────────

/// Forecast the timing of sending `msgsize` bytes starting at `now`.
///
/// Returns `(overall_forecast, fragment_forecasts, updated_state)`.  The
/// overall forecast spans the bounding interval across all fragments.
pub fn forecast_tcp_msg_send(
    props: &TcpConnProps,
    mut state: TcpState,
    now: Timestamp,
    msgsize: u64,
) -> (TcpMsgForecast, Vec<TcpMsgForecast>, TcpState) {
    let mut fragments: Vec<TcpMsgForecast> = Vec::new();
    let mut now = now;
    let mut remaining = msgsize;

    loop {
        if state.available_congestion_window == 0 {
            (now, state) = wait_for_ack(props, now, state);
            continue;
        }
        let send_size = remaining.min(state.available_congestion_window);
        let fragment = do_send(props, &mut state, now, send_size);
        now = fragment.send_trailing_edge;
        remaining -= send_size;
        fragments.push(fragment);
        if remaining == 0 {
            break;
        }
    }

    let merged = merge_adjacent_fragments(fragments);
    let overall = merged
        .iter()
        .cloned()
        .reduce(merge_forecasts)
        .expect("at least one fragment");
    (overall, merged, state)
}

/// Commit `send_size` bytes into the congestion window, derive timing, and
/// schedule the returning ACK.  Mutates `state` in-place.
fn do_send(
    props: &TcpConnProps,
    state: &mut TcpState,
    now: Timestamp,
    send_size: u64,
) -> TcpMsgForecast {
    let send_leading = now;
    let send_trailing = now + serialisation_time(props.bandwidth, send_size);
    let recv_leading = send_leading + props.latency;
    let recv_trailing = send_trailing + props.latency;
    // Strategic cheat: ACK is anchored to recv_leading, not recv_trailing.
    // Per-segment ACKs in real TCP start returning after one RTT (2 × latency);
    // using recv_trailing would add a full serialisation delay on top of that,
    // understating how quickly the sender can refill the congestion window.
    let ack_time = recv_leading + props.latency;

    state.available_congestion_window -= send_size;
    state.acknowledgements.push(Reverse((ack_time, send_size)));

    TcpMsgForecast {
        send_leading_edge: send_leading,
        send_trailing_edge: send_trailing,
        recv_leading_edge: recv_leading,
        recv_trailing_edge: recv_trailing,
        acknowledgement: ack_time,
        size: send_size,
    }
}

/// Pop the earliest pending ACK, advance `now` to its arrival time (if it
/// hasn't arrived yet), process it, and drain any further ACKs that have
/// already arrived by the new `now`.
fn wait_for_ack(props: &TcpConnProps, now: Timestamp, mut state: TcpState) -> (Timestamp, TcpState) {
    let Reverse((ack_ts, ack_bytes)) = state
        .acknowledgements
        .pop()
        .expect("congestion window exhausted with no pending ACKs");

    state = accum_ack(props, state, ack_bytes);

    if ack_ts <= now {
        // ACK already passed; drain any others that have arrived too.
        (now, drain_arrived_acks(props, now, state))
    } else {
        // Advance time to when this ACK lands; remaining queue is untouched.
        (ack_ts, state)
    }
}

/// Pop and apply all ACKs whose arrival timestamp ≤ `now`.
fn drain_arrived_acks(props: &TcpConnProps, now: Timestamp, mut state: TcpState) -> TcpState {
    loop {
        match state.acknowledgements.peek() {
            Some(Reverse((ts, _))) if *ts <= now => {
                let ack_bytes = state.acknowledgements.pop().unwrap().0 .1;
                state = accum_ack(props, state, ack_bytes);
            }
            _ => return state,
        }
    }
}

/// Release `ack_bytes` from the in-flight count.  While the congestion window
/// has not yet reached the receiver window (slow-start), also grow it.
fn accum_ack(props: &TcpConnProps, mut state: TcpState, ack_bytes: u64) -> TcpState {
    if state.congestion_window < props.receiver_window {
        // Slow-start: each ACK grows the congestion window by the same amount,
        // capped at the receiver window.
        let new_cwnd = (state.congestion_window + ack_bytes).min(props.receiver_window);
        let growth = new_cwnd - state.congestion_window;
        state.available_congestion_window += ack_bytes + growth;
        state.congestion_window = new_cwnd;
    } else {
        // Steady state: window is maxed at the receiver limit; just free the
        // bytes that the ACK confirms are no longer in flight.
        debug_assert_eq!(state.congestion_window, props.receiver_window);
        state.available_congestion_window += ack_bytes;
    }
    state
}

// ── Forecast helpers ─────────────────────────────────────────────────────────

/// Merge two logically-adjacent forecasts into one spanning both: leading
/// edges from `a`, trailing edges and ACK from `b`.
fn merge_forecasts(a: TcpMsgForecast, b: TcpMsgForecast) -> TcpMsgForecast {
    TcpMsgForecast {
        send_leading_edge: a.send_leading_edge,
        send_trailing_edge: b.send_trailing_edge,
        recv_leading_edge: a.recv_leading_edge,
        recv_trailing_edge: b.recv_trailing_edge,
        acknowledgement: b.acknowledgement,
        size: a.size + b.size,
    }
}

/// Collapse contiguous fragments — where the send trailing edge of one equals
/// the send leading edge of the next — into single forecasts.  This keeps the
/// fragment count bounded even across many window fills.
fn merge_adjacent_fragments(fragments: Vec<TcpMsgForecast>) -> Vec<TcpMsgForecast> {
    let mut merged: Vec<TcpMsgForecast> = Vec::new();
    for f in fragments {
        match merged.last_mut() {
            Some(last) if last.send_trailing_edge == f.send_leading_edge => {
                last.send_trailing_edge = f.send_trailing_edge;
                last.recv_trailing_edge = f.recv_trailing_edge;
                last.acknowledgement = f.acknowledgement;
                last.size += f.size;
            }
            _ => merged.push(f),
        }
    }
    merged
}

fn serialisation_time(bandwidth: u64, size: u64) -> Duration {
    Duration::from_secs_f64(size as f64 / bandwidth as f64)
}

// ── Trace ────────────────────────────────────────────────────────────────────

/// Simulate sending `messages` back-to-back from time 0 and return a trace
/// of `TcpEvent`s.  The first message starts at `Timestamp::zero()`.
pub fn trace_tcp_send(props: &TcpConnProps, messages: &[u64]) -> Vec<TcpEvent<()>> {
    let mut state = TcpState::default();
    let mut now = Timestamp::zero();
    let mut events = Vec::with_capacity(messages.len());

    for &msg_size in messages {
        let (overall, fragments, new_state) = forecast_tcp_msg_send(props, state, now, msg_size);
        now = overall.send_trailing_edge;
        state = new_state;
        events.push(TcpEvent {
            msg: (),
            overall,
            fragments,
        });
    }

    events
}

// ── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Bandwidth chosen so that serialisation_time(bandwidth, N) == N nanoseconds,
    /// making expected timestamps easy to compute exactly.
    const BW_NS_PER_BYTE: u64 = 1_000_000_000; // 1 GB/s

    fn props_with_latency_ms(latency_ms: u64) -> TcpConnProps {
        TcpConnProps::new(Duration::from_millis(latency_ms), BW_NS_PER_BYTE)
    }

    // ── Basic timing ────────────────────────────────────────────────────────

    #[test]
    fn small_message_fits_in_initial_window() {
        // 1000 bytes << 14600 byte initial window → one fragment, no waiting.
        let props = props_with_latency_ms(100);
        let (overall, fragments, _) =
            forecast_tcp_msg_send(&props, TcpState::default(), Timestamp::zero(), 1000);

        assert_eq!(fragments.len(), 1, "should be a single fragment");
        assert_eq!(overall.size, 1000);

        // serial_time = 1000 ns; latency = 100_000_000 ns
        let serial = Duration::from_nanos(1000);
        let lat = Duration::from_millis(100);

        assert_eq!(overall.send_leading_edge, Timestamp::zero());
        assert_eq!(overall.send_trailing_edge, Timestamp::zero() + serial);
        assert_eq!(overall.recv_leading_edge, Timestamp::zero() + lat);
        assert_eq!(overall.recv_trailing_edge, Timestamp::zero() + lat + serial);
        // Strategic cheat: ack = send_leading + 2 * latency (not + serial)
        assert_eq!(overall.acknowledgement, Timestamp::zero() + lat + lat);
    }

    #[test]
    fn timing_invariants_hold_for_every_fragment() {
        // Send 60 kB over a slow link (100 kB/s, 50 ms RTT) — forces several
        // window refills via slow-start.
        let props = TcpConnProps::new(Duration::from_millis(50), 100_000);
        let (_, fragments, _) =
            forecast_tcp_msg_send(&props, TcpState::default(), Timestamp::zero(), 60_000);

        for f in &fragments {
            assert!(f.send_leading_edge <= f.send_trailing_edge);
            // Leading edges always come from the same sub-fragment, so the
            // latency relationship holds exactly.
            assert_eq!(f.recv_leading_edge, f.send_leading_edge + props.latency);
            assert_eq!(f.recv_trailing_edge, f.send_trailing_edge + props.latency);
            // After merging, `acknowledgement` belongs to the last sub-fragment
            // while `send_leading_edge` is from the first, so we can only bound
            // it from below: ack ≥ send_leading + 2 × latency.
            assert!(f.acknowledgement >= f.send_leading_edge + props.latency + props.latency);
        }
    }

    // ── Fragmentation ────────────────────────────────────────────────────────

    #[test]
    fn large_message_is_fully_delivered() {
        // 5× the initial window forces at least one wait-for-ack cycle.
        let msgsize = 5 * INITIAL_CONGESTION_WINDOW;
        let props = props_with_latency_ms(100);
        let (overall, fragments, _) =
            forecast_tcp_msg_send(&props, TcpState::default(), Timestamp::zero(), msgsize);

        assert_eq!(overall.size, msgsize);
        assert_eq!(fragments.iter().map(|f| f.size).sum::<u64>(), msgsize);
        // More than one fragment because the initial window was exhausted.
        assert!(fragments.len() > 1, "expected fragmentation");
    }

    #[test]
    fn adjacent_fragments_are_merged() {
        // Adjacent fragments (no gap between sends) should be collapsed.
        let props = props_with_latency_ms(1); // tiny RTT → window refills immediately
        let (_, fragments, _) =
            forecast_tcp_msg_send(&props, TcpState::default(), Timestamp::zero(), 5 * INITIAL_CONGESTION_WINDOW);

        // With a 1 ms RTT, the congestion window grows quickly; all contiguous
        // sends should collapse to a small number of merged fragments.
        for w in fragments.windows(2) {
            assert_ne!(
                w[0].send_trailing_edge, w[1].send_leading_edge,
                "adjacent fragments should have been merged"
            );
        }
    }

    // ── Trace ────────────────────────────────────────────────────────────────

    #[test]
    fn trace_produces_one_event_per_message() {
        let props = props_with_latency_ms(50);
        let messages = vec![1000u64, 2000, 3000];
        let events = trace_tcp_send(&props, &messages);

        assert_eq!(events.len(), messages.len());
        for (event, &expected_size) in events.iter().zip(messages.iter()) {
            assert_eq!(event.overall.size, expected_size);
        }
    }

    #[test]
    fn trace_messages_are_sent_sequentially() {
        // Each message starts no earlier than the previous one ends.
        let props = props_with_latency_ms(50);
        let messages = vec![500u64; 5];
        let events = trace_tcp_send(&props, &messages);

        for w in events.windows(2) {
            assert!(
                w[1].overall.send_leading_edge >= w[0].overall.send_trailing_edge,
                "message {:?} starts before previous one ends",
                w[1].overall.send_leading_edge,
            );
        }
    }
}
