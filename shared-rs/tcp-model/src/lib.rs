//! Analytic envelope model of TCP transport effects.
//!
//! Provides per-link state that captures the *effects* of three transport
//! events on bandwidth and latency without simulating a TCP state machine:
//!
//! - **Cold start**: a slow-start ramp on first use of a link.
//! - **Idle reset**: the same ramp re-paid after a silent gap.
//! - **Loss**: a head-of-line stall for one RTO, followed by AIMD-style
//!   bandwidth recovery.
//!
//! Each event produces an [`Envelope`] with a bandwidth-multiplier curve
//! (depth, onset, release) and an additive latency stall. Envelopes overlay
//! on a per-link basis; the consumer queries [`LinkState::bw_mult`] and
//! [`LinkState::delivery_floor`] at message-send time to determine the
//! effective bandwidth and any HoL delivery floor.
//!
//! The crate is pure: no I/O, no async, no time source. Times are passed in
//! as [`std::time::Duration`] since a consumer-chosen link epoch.

pub mod config;
pub mod curve;
pub mod envelope;
pub mod link;

pub use config::LinkEnvelopeCfg;
pub use curve::{Curve, CurveSegment};
pub use envelope::Envelope;
pub use link::LinkState;
