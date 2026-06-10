//! TCP congestion-window channel — the Rust counterpart of Haskell's
//! `Chan/TCP.hs`.
//!
//! `TcpConnection<TMessage>` models one direction of a full-duplex TCP link.
//! Callers feed it messages via [`TcpConnection::send`]; the model applies
//! `forecast_tcp_msg_send` to derive arrival times and queues each message for
//! later retrieval via [`TcpConnection::recv_many`].
//!
//! ## Backpressure / serialisation ordering
//!
//! The Haskell implementation uses a one-slot `TMVar` as a send buffer,
//! preventing the next message from entering the serialiser until the current
//! one finishes.  Here we achieve the same effect with a `send_cursor`:
//! whenever a new message arrives we use `max(now, send_cursor)` as the
//! effective send time so that overlapping sends are automatically queued
//! behind their predecessor.
//!
//! ## Idle reset (RFC 6298 RTO)
//!
//! When the connection has been idle for longer than `max(1 s, RTT)` and all
//! in-flight ACKs have already arrived, the congestion window is reset to the
//! initial value — matching the Haskell `tcpIdleResetTime` logic.

use std::{collections::VecDeque, time::Duration};

use crate::{
    clock::Timestamp,
    tcp::{TcpConnProps, TcpState, forecast_tcp_msg_send},
};

/// Default bandwidth used when a TCP link has no explicit bandwidth cap.
/// 1000 kB/s ≈ 8 Mbit/s (matches Haskell `kibibytes 1000`).
pub const DEFAULT_TCP_BANDWIDTH: u64 = 1024 * 1000;

/// One directional TCP channel.  Pair two of these (one per direction) to
/// model a full-duplex link.
pub struct TcpConnection<TMessage> {
    props: TcpConnProps,
    state: TcpState,
    /// Earliest simulation time the serialiser is free for the next message.
    /// `None` until the first message is sent.
    send_cursor: Option<Timestamp>,
    /// Messages awaiting delivery, ordered by arrival time.
    latency_queue: VecDeque<(TMessage, Timestamp)>,
}

impl<TMessage> TcpConnection<TMessage> {
    pub fn new(props: TcpConnProps) -> Self {
        Self {
            props,
            state: TcpState::default(),
            send_cursor: None,
            latency_queue: VecDeque::new(),
        }
    }

    /// Serialise `message` (`bytes` bytes) into the TCP stream at time `now`.
    ///
    /// If the serialiser is still busy from a previous message the send is
    /// delayed until it is free.  The message is then queued with its computed
    /// arrival time (`recv_trailing_edge` from the forecast).
    pub fn send(&mut self, message: TMessage, bytes: u64, now: Timestamp) {
        let effective_now = match self.send_cursor {
            Some(cursor) => {
                // Idle reset: if the link has been quiet for longer than the
                // RTO threshold and all in-flight ACKs have returned, reset
                // the congestion window (RFC 6298).
                let idle_threshold =
                    Duration::from_secs(1).max(self.props.latency * 2);
                if now >= cursor + idle_threshold && self.state.all_acks_arrived(now) {
                    self.state = TcpState::default();
                }
                now.max(cursor)
            }
            None => now,
        };

        let old_state = std::mem::take(&mut self.state);
        let (forecast, _, new_state) =
            forecast_tcp_msg_send(&self.props, old_state, effective_now, bytes);
        self.state = new_state;
        self.send_cursor = Some(forecast.send_trailing_edge);
        self.latency_queue
            .push_back((message, forecast.recv_trailing_edge));
    }

    pub fn next_arrival_time(&self) -> Option<Timestamp> {
        self.latency_queue.front().map(|(_, ts)| *ts)
    }

    pub fn recv_many(&mut self, now: Timestamp) -> Vec<(TMessage, Timestamp)> {
        let mut results = Vec::new();
        while self
            .latency_queue
            .front()
            .is_some_and(|(_, ts)| *ts <= now)
        {
            results.push(self.latency_queue.pop_front().unwrap());
        }
        results
    }

    /// Returns `(message_count, queued_bytes)`.
    /// Byte tracking is not available for the latency queue so bytes is 0.
    pub fn queue_stats(&self) -> (usize, u64) {
        (self.latency_queue.len(), 0)
    }
}
