//! Shapes for the onset and release of an [`Envelope`](crate::envelope::Envelope).
//!
//! A [`CurveSegment`] interpolates between two scalar values over a fixed
//! duration. Three shapes are supported:
//!
//! - [`Curve::Step`]: constant at `start` until the segment expires, then `end`.
//! - [`Curve::Linear`]: arithmetic interpolation.
//! - [`Curve::Geometric`]: log-space interpolation (`start^(1-t) * end^t`).
//!   Useful for bandwidth-multiplier curves whose natural shape is exponential
//!   (e.g. TCP slow-start). Degenerate when either endpoint is zero — in that
//!   case the segment is held at zero for all `t > 0` regardless of the
//!   intended shape, so callers should keep both endpoints in `(0, 1]`.

use std::time::Duration;

use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Curve {
    Step,
    Linear,
    Geometric,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct CurveSegment {
    pub duration: Duration,
    pub shape: Curve,
}

impl CurveSegment {
    pub fn new(duration: Duration, shape: Curve) -> Self {
        Self { duration, shape }
    }

    /// Interpolate from `start` to `end` over this segment, given the time
    /// elapsed since the segment began. Returns `end` once `elapsed` meets
    /// or exceeds the segment duration.
    pub fn interp(&self, start: f64, end: f64, elapsed: Duration) -> f64 {
        if self.duration.is_zero() || elapsed >= self.duration {
            return end;
        }
        let t = elapsed.as_secs_f64() / self.duration.as_secs_f64();
        match self.shape {
            Curve::Step => start,
            Curve::Linear => start + t * (end - start),
            Curve::Geometric => start.powf(1.0 - t) * end.powf(t),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const D: Duration = Duration::from_millis(1000);

    fn approx(a: f64, b: f64, eps: f64) {
        assert!((a - b).abs() < eps, "{a} != {b} (eps {eps})");
    }

    #[test]
    fn step_holds_start_until_end() {
        let seg = CurveSegment::new(D, Curve::Step);
        assert_eq!(seg.interp(1.0, 0.1, Duration::ZERO), 1.0);
        assert_eq!(seg.interp(1.0, 0.1, Duration::from_millis(500)), 1.0);
        assert_eq!(seg.interp(1.0, 0.1, Duration::from_millis(999)), 1.0);
        assert_eq!(seg.interp(1.0, 0.1, D), 0.1);
        assert_eq!(seg.interp(1.0, 0.1, Duration::from_millis(1500)), 0.1);
    }

    #[test]
    fn linear_endpoints_and_midpoint() {
        let seg = CurveSegment::new(D, Curve::Linear);
        approx(seg.interp(1.0, 0.1, Duration::ZERO), 1.0, 1e-12);
        approx(seg.interp(1.0, 0.1, D), 0.1, 1e-12);
        approx(seg.interp(1.0, 0.1, Duration::from_millis(500)), 0.55, 1e-12);
    }

    #[test]
    fn geometric_midpoint_is_geometric_mean() {
        let seg = CurveSegment::new(D, Curve::Geometric);
        approx(seg.interp(1.0, 0.01, Duration::ZERO), 1.0, 1e-12);
        approx(seg.interp(1.0, 0.01, D), 0.01, 1e-12);
        approx(
            seg.interp(1.0, 0.01, Duration::from_millis(500)),
            (1.0_f64 * 0.01).sqrt(),
            1e-12,
        );
    }

    #[test]
    fn geometric_collapses_when_endpoint_is_zero() {
        let seg = CurveSegment::new(D, Curve::Geometric);
        // start = 0: held at 0 for all t > 0, jumps to end at t = duration
        assert_eq!(seg.interp(0.0, 1.0, Duration::ZERO), 0.0);
        assert_eq!(seg.interp(0.0, 1.0, Duration::from_millis(500)), 0.0);
        assert_eq!(seg.interp(0.0, 1.0, D), 1.0);
    }

    #[test]
    fn zero_duration_returns_end_immediately() {
        let seg = CurveSegment::new(Duration::ZERO, Curve::Linear);
        assert_eq!(seg.interp(1.0, 0.5, Duration::ZERO), 0.5);
    }
}
