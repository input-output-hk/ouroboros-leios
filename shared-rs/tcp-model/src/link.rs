//! Per-link envelope state.
//!
//! Each directed link carries its own [`LinkState`]. Consumers call
//! [`LinkState::on_send`] before queueing a new message: this prunes expired
//! envelopes, fires a cold-start or idle-reset envelope when appropriate, and
//! draws packet loss. At any other moment they can query
//! [`LinkState::bw_mult`] (the multiplier on nominal bandwidth) and
//! [`LinkState::delivery_floor`] (an absolute time below which arrivals must
//! not be reported).

use std::time::Duration;

use rand::Rng;
use rand::rngs::StdRng;
use smallvec::SmallVec;

use crate::config::LinkEnvelopeCfg;
use crate::curve::{Curve, CurveSegment};
use crate::envelope::Envelope;

const INTEGRATE_STEPS: u32 = 16;

pub struct LinkState {
    cfg: LinkEnvelopeCfg,
    rng: StdRng,
    last_traffic: Option<Duration>,
    active: SmallVec<[Envelope; 4]>,
}

impl LinkState {
    pub fn new(cfg: LinkEnvelopeCfg, rng: StdRng) -> Self {
        Self {
            cfg,
            rng,
            last_traffic: None,
            active: SmallVec::new(),
        }
    }

    pub fn cfg(&self) -> &LinkEnvelopeCfg {
        &self.cfg
    }

    /// Product of every active envelope's bandwidth multiplier at `t`.
    pub fn bw_mult(&self, t: Duration) -> f64 {
        self.active.iter().map(|e| e.bw_mult_at(t)).product()
    }

    /// Latest stall-window end-time among active envelopes whose stall window
    /// covers `t`. If none, returns `t` itself — the arrival is unaffected.
    pub fn delivery_floor(&self, t: Duration) -> Duration {
        self.active
            .iter()
            .filter_map(|e| e.delivery_floor_at(t))
            .max()
            .unwrap_or(t)
    }

    /// Called before a new message is queued for transmission. Drops expired
    /// envelopes, fires a cold or idle envelope when applicable, and draws a
    /// loss event whose probability scales with the message's segment count.
    pub fn on_send(&mut self, t: Duration, bytes: u64) {
        self.active.retain(|e| !e.is_expired_at(t));

        let trigger_cold = match self.last_traffic {
            None => true,
            Some(prev) => t.checked_sub(prev).is_some_and(|gap| gap > self.cfg.idle_reset_threshold),
        };
        if trigger_cold {
            self.active.push(self.cold_envelope(t));
        }

        if self.draw_loss(bytes) {
            self.active.push(self.loss_envelope(t));
        }

        self.last_traffic = Some(t);
    }

    /// Integrates `bps · bw_mult(s)` over `[t0, t1]`. Sub-divides at every
    /// active envelope's phase transition, then applies a composite trapezoid
    /// rule with [`INTEGRATE_STEPS`] sub-steps inside each phase-stable piece
    /// so that geometric release curves are approximated accurately enough
    /// for sim-realism use.
    pub fn bytes_deliverable(&self, bps: u64, t0: Duration, t1: Duration) -> u64 {
        if t1 <= t0 || bps == 0 {
            return 0;
        }
        let mut breaks: SmallVec<[Duration; 16]> = SmallVec::new();
        breaks.push(t0);
        for e in &self.active {
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
            bw_depth: self.cfg.cold_bw_depth,
            bw_onset: CurveSegment::new(Duration::ZERO, Curve::Step),
            bw_release: CurveSegment::new(self.cfg.cold_release, self.cfg.cold_release_shape),
            lat_stall: Duration::ZERO,
        }
    }

    fn loss_envelope(&self, t: Duration) -> Envelope {
        Envelope {
            fired_at: t,
            bw_depth: self.cfg.loss_bw_depth,
            // Onset holds bw at 1.0 throughout the RTO stall (delivery floor
            // masks any transmission), then steps to depth as recovery begins.
            bw_onset: CurveSegment::new(self.cfg.rto, Curve::Step),
            bw_release: CurveSegment::new(self.cfg.loss_release, self.cfg.loss_release_shape),
            lat_stall: self.cfg.rto,
        }
    }

    fn draw_loss(&mut self, bytes: u64) -> bool {
        if self.cfg.loss_prob_per_segment <= 0.0 || bytes == 0 {
            return false;
        }
        let segments = bytes.div_ceil(self.cfg.mss_bytes) as f64;
        let p_msg = 1.0 - (1.0 - self.cfg.loss_prob_per_segment).powf(segments);
        self.rng.gen::<f64>() < p_msg
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;

    fn ms(n: u64) -> Duration {
        Duration::from_millis(n)
    }

    fn rng() -> StdRng {
        StdRng::seed_from_u64(0xC0FFEE)
    }

    #[test]
    fn fresh_link_fires_cold_envelope_on_first_send() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let mut s = LinkState::new(cfg, rng());
        s.on_send(ms(0), 1500);
        assert_eq!(s.active.len(), 1);
        // Step onset → mult at t=0 is `depth`, well below 1.0.
        assert!(s.bw_mult(ms(0)) < 0.2);
    }

    #[test]
    fn second_send_within_idle_threshold_does_not_re_fire() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let mut s = LinkState::new(cfg, rng());
        s.on_send(ms(0), 1500);
        let cold_release_end = ms(0) + s.cfg.cold_release;
        // Second send inside the cold envelope's recovery and well inside
        // the idle threshold: only the original envelope is active.
        s.on_send(cold_release_end / 2, 1500);
        assert_eq!(s.active.len(), 1);
    }

    #[test]
    fn long_idle_gap_re_fires_cold_envelope() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let mut s = LinkState::new(cfg, rng());
        s.on_send(ms(0), 1500);
        let before = s.active.len();
        let later = s.cfg.idle_reset_threshold + ms(100);
        s.on_send(later, 1500);
        // A new cold envelope has been pushed; the old one may still be
        // mid-release if its recovery is longer than the idle threshold.
        assert!(s.active.len() > before);
        assert!(s.bw_mult(later) < 0.2);
    }

    #[test]
    fn loss_disabled_by_default() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let mut s = LinkState::new(cfg, rng());
        for i in 0..1000 {
            s.on_send(ms(i * 10), 1500);
        }
        // Without loss, only one envelope at a time is active (cold/idle).
        assert!(s.active.len() <= 1);
    }

    #[test]
    fn loss_certain_always_fires() {
        let mut cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        cfg.loss_prob_per_segment = 1.0;
        let mut s = LinkState::new(cfg, rng());
        s.on_send(ms(0), 1500);
        // Cold + loss envelopes both active.
        assert_eq!(s.active.len(), 2);
    }

    #[test]
    fn delivery_floor_unblocked_outside_stall() {
        let mut cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        cfg.loss_prob_per_segment = 1.0;
        let rto = cfg.rto;
        let mut s = LinkState::new(cfg, rng());
        s.on_send(ms(100), 1500);
        // Inside the rto stall → floor at fired_at + rto.
        assert_eq!(s.delivery_floor(ms(500)), ms(100) + rto);
        // After stall → no floor.
        assert_eq!(s.delivery_floor(ms(2000)), ms(2000));
    }

    #[test]
    fn bytes_deliverable_zero_envelopes_is_linear() {
        let cfg = LinkEnvelopeCfg::disabled();
        let s = LinkState::new(cfg, rng());
        let bytes = s.bytes_deliverable(1_000_000, ms(0), ms(100));
        // 100ms at 1MB/s = 100_000 bytes.
        assert_eq!(bytes, 100_000);
    }

    #[test]
    fn bytes_deliverable_under_cold_envelope_is_below_linear() {
        let cfg = LinkEnvelopeCfg::defaults_for(ms(150), 1_000_000);
        let mut s = LinkState::new(cfg, rng());
        s.on_send(ms(0), 1);
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
        let mut s = LinkState::new(LinkEnvelopeCfg::defaults_for(lat, bps), rng());
        s.on_send(Duration::ZERO, 1);

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
