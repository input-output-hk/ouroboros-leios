//! A single transport event represented as overlaid bandwidth and latency
//! envelopes that decay back to their nominal values.
//!
//! There is at most one [`Envelope`] active per directed link at any moment
//! — TCP has a single cwnd per connection, and a new event (loss or idle
//! reset) re-triggers the envelope from whatever multiplier the link is
//! currently sitting at. Composing event effects is therefore an in-place
//! replacement (capturing the current mult as the next envelope's
//! `bw_start`), not a stack of overlaid contributions.

use std::time::Duration;

use crate::curve::CurveSegment;

#[derive(Clone, Copy, Debug)]
pub struct Envelope {
    pub fired_at: Duration,
    /// Multiplier at `fired_at`. For a cold/idle envelope this is `1.0`. For
    /// a loss event that fires mid-recovery it is the multiplier that was in
    /// effect just before the loss — the new envelope picks up from there.
    pub bw_start: f64,
    /// Multiplier at the end of the onset segment (the "bottom" of the dip).
    pub bw_depth: f64,
    pub bw_onset: CurveSegment,
    pub bw_release: CurveSegment,
    /// Width of the delivery-floor window. Any arrival landing in
    /// `[fired_at, fired_at + lat_stall]` is bumped to its end. Zero means
    /// no latency effect.
    pub lat_stall: Duration,
}

impl Envelope {
    /// Bandwidth multiplier contributed by this envelope at absolute time `t`
    /// (`Duration` since the link epoch). Returns `1.0` once the envelope has
    /// fully released.
    pub fn bw_mult_at(&self, t: Duration) -> f64 {
        let Some(elapsed) = t.checked_sub(self.fired_at) else {
            return 1.0;
        };
        if elapsed < self.bw_onset.duration {
            self.bw_onset.interp(self.bw_start, self.bw_depth, elapsed)
        } else {
            let since_release = elapsed - self.bw_onset.duration;
            if since_release < self.bw_release.duration {
                self.bw_release.interp(self.bw_depth, 1.0, since_release)
            } else {
                1.0
            }
        }
    }

    /// If `t` falls inside the stall window, the absolute time to which
    /// arrivals should be deferred; otherwise `None`.
    pub fn delivery_floor_at(&self, t: Duration) -> Option<Duration> {
        if self.lat_stall.is_zero() {
            return None;
        }
        let stall_end = self.fired_at + self.lat_stall;
        if t < self.fired_at || t >= stall_end {
            None
        } else {
            Some(stall_end)
        }
    }

    /// True once both bandwidth phases have completed and the stall window
    /// has closed — the envelope can be dropped from active state.
    pub fn is_expired_at(&self, t: Duration) -> bool {
        let bw_end = self.fired_at + self.bw_onset.duration + self.bw_release.duration;
        let stall_end = self.fired_at + self.lat_stall;
        t >= bw_end && t >= stall_end
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::curve::Curve;

    fn ms(n: u64) -> Duration {
        Duration::from_millis(n)
    }

    fn env() -> Envelope {
        Envelope {
            fired_at: ms(1000),
            bw_start: 1.0,
            bw_depth: 0.1,
            bw_onset: CurveSegment::new(Duration::ZERO, Curve::Step),
            bw_release: CurveSegment::new(ms(500), Curve::Linear),
            lat_stall: ms(200),
        }
    }

    #[test]
    fn bw_mult_before_fired_is_unit() {
        assert_eq!(env().bw_mult_at(ms(500)), 1.0);
    }

    #[test]
    fn bw_mult_step_onset_jumps_to_depth() {
        // Zero-duration onset → release begins at fired_at with mult = depth.
        let e = env();
        assert!((e.bw_mult_at(ms(1000)) - 0.1).abs() < 1e-12);
    }

    #[test]
    fn bw_mult_linear_release_midpoint() {
        let e = env();
        // 250ms into the 500ms release, halfway between 0.1 and 1.0.
        assert!((e.bw_mult_at(ms(1250)) - 0.55).abs() < 1e-12);
    }

    #[test]
    fn bw_mult_after_release_returns_unit() {
        let e = env();
        assert_eq!(e.bw_mult_at(ms(1600)), 1.0);
    }

    #[test]
    fn delivery_floor_inside_window() {
        let e = env();
        assert_eq!(e.delivery_floor_at(ms(1100)), Some(ms(1200)));
    }

    #[test]
    fn delivery_floor_outside_window() {
        let e = env();
        assert_eq!(e.delivery_floor_at(ms(900)), None);
        assert_eq!(e.delivery_floor_at(ms(1200)), None);
        assert_eq!(e.delivery_floor_at(ms(1500)), None);
    }

    #[test]
    fn loss_during_recovery_starts_from_current_mult() {
        // A loss firing while bw is already at 0.4 (mid recovery from
        // something earlier) should hold at 0.4 through the stall window,
        // then drop to 0.4 * 0.5 = 0.2, then recover linearly to 1.0.
        let e = Envelope {
            fired_at: ms(1000),
            bw_start: 0.4,
            bw_depth: 0.2,
            bw_onset: CurveSegment::new(ms(1000), Curve::Step), // RTO stall
            bw_release: CurveSegment::new(ms(2000), Curve::Linear),
            lat_stall: ms(1000),
        };
        assert!((e.bw_mult_at(ms(1500)) - 0.4).abs() < 1e-12);     // mid-stall
        assert!((e.bw_mult_at(ms(2000)) - 0.2).abs() < 1e-12);     // stall end → depth
        assert!((e.bw_mult_at(ms(3000)) - 0.6).abs() < 1e-12);     // halfway recovery
        assert!((e.bw_mult_at(ms(4000)) - 1.0).abs() < 1e-12);     // fully recovered
    }

    #[test]
    fn expiration_requires_both_bw_and_stall_to_close() {
        let mut e = env();
        e.lat_stall = ms(800);
        assert!(!e.is_expired_at(ms(1400))); // bw done at 1500, stall ends 1800
        assert!(!e.is_expired_at(ms(1700)));
        assert!(e.is_expired_at(ms(1800)));
    }
}
