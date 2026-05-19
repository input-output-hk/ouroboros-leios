//! Per-link envelope state.
//!
//! Each directed link carries its own [`LinkState`] holding at most one
//! [`Envelope`] — TCP has a single cwnd per connection, and loss or idle
//! events *re-trigger* the envelope rather than overlay onto a stack.
//! Consumers call [`LinkState::on_send`] before queueing a new message:
//! that prunes the envelope if it has fully released, fires a cold/idle
//! envelope when applicable, and replaces the envelope with a fresh loss
//! event when the caller's pre-drawn `loss_drawn` flag is set. Replacement
//! captures the current multiplier as the new envelope's `bw_start` so the
//! ramp continues smoothly from wherever the link was at the moment of the
//! event.
//!
//! Randomness is the consumer's responsibility: see
//! [`LinkEnvelopeCfg::msg_loss_prob`] for the per-message probability to
//! Bernoulli-sample from any deterministic oracle.

use std::time::Duration;

use smallvec::SmallVec;

use crate::config::LinkEnvelopeCfg;
use crate::curve::{Curve, CurveSegment};
use crate::envelope::Envelope;

const INTEGRATE_STEPS: u32 = 16;

pub struct LinkState {
    cfg: LinkEnvelopeCfg,
    last_traffic: Option<Duration>,
    current: Option<Envelope>,
}

impl LinkState {
    pub fn new(cfg: LinkEnvelopeCfg) -> Self {
        Self {
            cfg,
            last_traffic: None,
            current: None,
        }
    }

    pub fn cfg(&self) -> &LinkEnvelopeCfg {
        &self.cfg
    }

    /// Multiplier on nominal bandwidth at time `t`. `1.0` when no envelope
    /// is active or the active envelope has fully released.
    pub fn bw_mult(&self, t: Duration) -> f64 {
        self.current.as_ref().map(|e| e.bw_mult_at(t)).unwrap_or(1.0)
    }

    /// Stall-window end-time if `t` lies inside an active stall, else `t`.
    pub fn delivery_floor(&self, t: Duration) -> Duration {
        self.current
            .as_ref()
            .and_then(|e| e.delivery_floor_at(t))
            .unwrap_or(t)
    }

    /// Called before a new message is queued for transmission. Clears the
    /// envelope if it has fully released, fires a cold/idle envelope when
    /// applicable, and replaces it with a fresh loss envelope (capturing
    /// the current mult as `bw_start`) when `loss_drawn` is true. Envelopes
    /// that would be born immediately expired (e.g. under
    /// [`LinkEnvelopeCfg::disabled`]) are dropped at birth — callers can
    /// rely on [`Self::has_active_envelopes`] being false in that case.
    pub fn on_send(&mut self, t: Duration, _bytes: u64, loss_drawn: bool) {
        if self.current.as_ref().is_some_and(|e| e.is_expired_at(t)) {
            self.current = None;
        }

        let trigger_cold = self.current.is_none()
            && match self.last_traffic {
                None => true,
                Some(prev) => t
                    .checked_sub(prev)
                    .is_some_and(|gap| gap > self.cfg.idle_reset_threshold),
            };
        if trigger_cold {
            let env = self.cold_envelope(t);
            if !env.is_expired_at(t) {
                self.current = Some(env);
            }
        }

        if loss_drawn {
            let mult_now = self.bw_mult(t);
            // Preserve any unfinished stall window from a prior loss event —
            // a new loss can extend it but never shorten it.
            let existing_stall_end = self
                .current
                .as_ref()
                .map(|e| e.fired_at + e.lat_stall)
                .filter(|end| *end > t)
                .unwrap_or(t);
            let new_stall_end = t + self.cfg.rto;
            let lat_stall = existing_stall_end.max(new_stall_end) - t;
            let env = self.loss_envelope(t, mult_now, lat_stall);
            if !env.is_expired_at(t) {
                self.current = Some(env);
            }
        }

        self.last_traffic = Some(t);
    }

    /// True iff an envelope is currently in effect. Plural in the name is a
    /// historical hold-over from a stacked design; there is at most one.
    pub fn has_active_envelopes(&self) -> bool {
        self.current.is_some()
    }

    /// Smallest `t ≥ t0` such that [`Self::bytes_deliverable`]`(bps, t0, t)`
    /// reaches `target`. Returns `t0` when the target is zero; returns the
    /// supplied `upper` if even `bytes_deliverable(t0, upper)` falls short.
    /// Useful for projecting when a specific number of bytes will have been
    /// delivered through an envelope-modulated pipe.
    pub fn invert_bytes_deliverable(
        &self,
        bps: u64,
        target: u64,
        t0: Duration,
        upper: Duration,
    ) -> Duration {
        if target == 0 || bps == 0 {
            return t0;
        }
        if upper <= t0 || self.bytes_deliverable(bps, t0, upper) < target {
            return upper;
        }
        let mut lo = t0;
        let mut hi = upper;
        let tolerance = Duration::from_micros(1);
        while hi.saturating_sub(lo) > tolerance {
            let mid = lo + (hi - lo) / 2;
            if self.bytes_deliverable(bps, t0, mid) >= target {
                hi = mid;
            } else {
                lo = mid;
            }
        }
        hi
    }

    /// Integrates `bps · bw_mult(s)` over `[t0, t1]`. Sub-divides at the
    /// active envelope's phase transitions, then applies a composite
    /// trapezoid rule with [`INTEGRATE_STEPS`] sub-steps inside each
    /// phase-stable piece so that geometric release curves integrate
    /// accurately enough for sim-realism use.
    pub fn bytes_deliverable(&self, bps: u64, t0: Duration, t1: Duration) -> u64 {
        if t1 <= t0 || bps == 0 {
            return 0;
        }
        let mut breaks: SmallVec<[Duration; 4]> = SmallVec::new();
        breaks.push(t0);
        if let Some(e) = &self.current {
            let onset_end = e.fired_at + e.bw_onset.duration;
            let release_end = onset_end + e.bw_release.duration;
            for b in [e.fired_at, onset_end, release_end] {
                if b > t0 && b < t1 {
                    breaks.push(b);
                }
            }
        }
        breaks.push(t1);
        breaks.sort();
        breaks.dedup();

        let bps_f = bps as f64;
        let mut bytes = 0.0;
        for window in breaks.windows(2) {
            let (a, b) = (window[0], window[1]);
            let span = (b - a).as_secs_f64();
            let dt = span / INTEGRATE_STEPS as f64;
            let mut prev = self.bw_mult(a);
            for i in 1..=INTEGRATE_STEPS {
                let next_t = a + Duration::from_secs_f64(dt * i as f64);
                let next = self.bw_mult(next_t);
                bytes += bps_f * (prev + next) * 0.5 * dt;
                prev = next;
            }
        }
        bytes.max(0.0) as u64
    }

    fn cold_envelope(&self, t: Duration) -> Envelope {
        Envelope {
            fired_at: t,
            bw_start: 1.0,
            bw_depth: self.cfg.cold_bw_depth,
            bw_onset: CurveSegment::new(Duration::ZERO, Curve::Step),
            bw_release: CurveSegment::new(self.cfg.cold_release, self.cfg.cold_release_shape),
            lat_stall: Duration::ZERO,
        }
    }

    fn loss_envelope(&self, t: Duration, start_mult: f64, lat_stall: Duration) -> Envelope {
        let depth = (start_mult * self.cfg.loss_bw_depth).max(1e-6).min(start_mult);
        Envelope {
            fired_at: t,
            bw_start: start_mult,
            bw_depth: depth,
            // Onset holds bw at `start_mult` through the RTO stall (delivery
            // floor masks any transmission anyway), then steps to depth as
            // recovery begins.
            bw_onset: CurveSegment::new(self.cfg.rto, Curve::Step),
            bw_release: CurveSegment::new(self.cfg.loss_release, self.cfg.loss_release_shape),
            lat_stall,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ms(n: u64) -> Duration {
        Duration::from_millis(n)
    }

    #[test]
    fn fresh_link_fires_cold_envelope_on_first_send() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let mut s = LinkState::new(cfg);
        s.on_send(ms(0), 1500, false);
        assert!(s.has_active_envelopes());
        // Step onset → mult at t=0 is `depth`, well below 1.0.
        assert!(s.bw_mult(ms(0)) < 0.2);
    }

    #[test]
    fn second_send_within_idle_threshold_does_not_re_fire() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let mut s = LinkState::new(cfg);
        s.on_send(ms(0), 1500, false);
        let original_fired = s.current.as_ref().unwrap().fired_at;
        let cold_release_end = ms(0) + s.cfg.cold_release;
        s.on_send(cold_release_end / 2, 1500, false);
        // Still the original cold envelope — no re-trigger.
        assert_eq!(s.current.as_ref().unwrap().fired_at, original_fired);
    }

    #[test]
    fn long_idle_gap_re_fires_cold_envelope_after_release() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let mut s = LinkState::new(cfg);
        s.on_send(ms(0), 1500, false);
        // Past the cold envelope's release end AND past the idle threshold.
        let later = s.cfg.cold_release + s.cfg.idle_reset_threshold + ms(100);
        s.on_send(later, 1500, false);
        let env = s.current.as_ref().unwrap();
        assert_eq!(env.fired_at, later);
        assert!(s.bw_mult(later) < 0.2);
    }

    #[test]
    fn loss_replaces_envelope_and_picks_up_from_current_mult() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let mut s = LinkState::new(cfg);
        // Fire cold envelope, advance partway through its recovery.
        s.on_send(ms(0), 1500, false);
        let t_loss = s.cfg.cold_release / 2;
        let mult_before_loss = s.bw_mult(t_loss);
        assert!(mult_before_loss > s.cfg.cold_bw_depth && mult_before_loss < 1.0);
        s.on_send(t_loss, 1500, true);
        let env = s.current.as_ref().unwrap();
        assert_eq!(env.fired_at, t_loss);
        // bw_start captured the recovery-phase multiplier; depth halved it.
        assert!((env.bw_start - mult_before_loss).abs() < 1e-9);
        assert!((env.bw_depth - mult_before_loss * 0.5).abs() < 1e-9);
    }

    #[test]
    fn back_to_back_losses_extend_stall_window() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let mut s = LinkState::new(cfg);
        let rto = s.cfg.rto;
        s.on_send(ms(0), 1500, true);
        // Stall ends at t = rto.
        assert_eq!(s.delivery_floor(rto / 2), rto);
        // Second loss 200ms later → new stall ends at 200ms + rto, which is
        // longer than the prior end. The replacement must honour that.
        s.on_send(ms(200), 1500, true);
        assert_eq!(s.delivery_floor(ms(300)), ms(200) + rto);
    }

    #[test]
    fn delivery_floor_unblocked_outside_stall() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let rto = cfg.rto;
        let mut s = LinkState::new(cfg);
        s.on_send(ms(100), 1500, true);
        // Inside the rto stall → floor at fired_at + rto.
        assert_eq!(s.delivery_floor(ms(500)), ms(100) + rto);
        // After stall → no floor.
        assert_eq!(s.delivery_floor(ms(2000)), ms(2000));
    }

    #[test]
    fn bytes_deliverable_zero_envelopes_is_linear() {
        let s = LinkState::new(LinkEnvelopeCfg::disabled());
        let bytes = s.bytes_deliverable(1_000_000, ms(0), ms(100));
        // 100ms at 1MB/s = 100_000 bytes.
        assert_eq!(bytes, 100_000);
    }

    #[test]
    fn bytes_deliverable_under_cold_envelope_is_below_linear() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let mut s = LinkState::new(cfg);
        s.on_send(ms(0), 1, false);
        let bytes = s.bytes_deliverable(1_000_000, ms(0), ms(200));
        // 200ms at 1MB/s, depth ≈ 0.05 ramping up → much less than 200_000.
        assert!(bytes < 100_000, "got {bytes}");
    }

    #[test]
    fn slow_start_ramp_matches_analytic_estimate() {
        // 300ms latency, 1 MiB/s, 1 MB cold message. Analytic transfer time
        // through slow-start is ~3.4s (vs ~1.0s with full bw); add latency
        // for total arrival around 3.7s. Compare to a binary search over
        // `bytes_deliverable` and assert the integrator lands in a sane band.
        let lat = ms(300);
        let bps: u64 = 1_024_000;
        let mut s = LinkState::new(LinkEnvelopeCfg::defaults_for(lat, bps));
        s.on_send(Duration::ZERO, 1, false);

        let target: u64 = 1_048_576;
        let (mut lo, mut hi) = (Duration::ZERO, Duration::from_secs(10));
        while hi - lo > Duration::from_micros(500) {
            let mid = (lo + hi) / 2;
            if s.bytes_deliverable(bps, Duration::ZERO, mid) < target {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        let transfer = lo;
        assert!(
            transfer >= Duration::from_millis(3000) && transfer <= Duration::from_millis(3800),
            "transfer {transfer:?} outside [3.0s, 3.8s]"
        );
    }
}
