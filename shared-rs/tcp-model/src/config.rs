//! Per-link configuration for the envelope model.

use std::time::Duration;

use serde::{Deserialize, Serialize};

use crate::curve::Curve;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LinkEnvelopeCfg {
    pub mss_bytes: u64,
    pub initial_cwnd_segments: u32,
    pub idle_reset_threshold: Duration,
    pub rto: Duration,
    pub loss_prob_per_segment: f64,
    pub loss_bw_depth: f64,
    pub cold_bw_depth: f64,
    pub cold_release: Duration,
    pub cold_release_shape: Curve,
    pub loss_release: Duration,
    pub loss_release_shape: Curve,
}

impl LinkEnvelopeCfg {
    /// Defaults derived from the link's nominal one-way latency and bandwidth.
    /// Requires `bps > 0` and `latency` strictly positive — for a disabled
    /// envelope use [`Self::disabled`] instead.
    pub fn defaults_for(latency: Duration, bps: u64) -> Self {
        assert!(bps > 0, "bps must be > 0");
        assert!(!latency.is_zero(), "latency must be > 0");

        let mss_bytes: u64 = 1460;
        let initial_cwnd_segments: u32 = 10;
        let iw_bytes = (initial_cwnd_segments as u64) * mss_bytes;
        let latency_s = latency.as_secs_f64();
        let bdp_bytes = (bps as f64) * latency_s;

        // Cold/idle envelope: depth = IW / (2·BDP), release = log2(2·BDP/IW)·2L.
        // If IW already covers 2·BDP, slow-start has nothing to do.
        let (cold_bw_depth, cold_release) = if bdp_bytes * 2.0 <= iw_bytes as f64 {
            (1.0, Duration::ZERO)
        } else {
            let depth = (iw_bytes as f64) / (2.0 * bdp_bytes);
            let rtts = (2.0 * bdp_bytes / iw_bytes as f64).log2();
            let release = Duration::from_secs_f64(rtts * 2.0 * latency_s);
            (depth.clamp(1e-6, 1.0), release)
        };

        // Loss envelope (AIMD shape): bw halves at the moment of loss and
        // recovers linearly over BDP/(2·MSS) RTTs.
        let loss_rtts = bdp_bytes / 2.0 / mss_bytes as f64;
        let loss_release = Duration::from_secs_f64(loss_rtts.max(0.0) * 2.0 * latency_s);

        let threshold = Duration::from_secs(1).max(2 * latency);

        Self {
            mss_bytes,
            initial_cwnd_segments,
            idle_reset_threshold: threshold,
            rto: threshold,
            loss_prob_per_segment: 0.0,
            loss_bw_depth: 0.5,
            cold_bw_depth,
            cold_release,
            cold_release_shape: Curve::Geometric,
            loss_release,
            loss_release_shape: Curve::Linear,
        }
    }

    /// Effective per-message loss probability under independent per-segment
    /// drops. Returns `0.0` when either input is zero. Consumers draw a
    /// uniform random `u ∈ [0, 1)` and pass `u < msg_loss_prob(bytes)` as
    /// the `loss_drawn` argument to [`crate::LinkState::on_send`].
    pub fn msg_loss_prob(&self, bytes: u64) -> f64 {
        if self.loss_prob_per_segment <= 0.0 || bytes == 0 || self.mss_bytes == 0 {
            return 0.0;
        }
        let segments = bytes.div_ceil(self.mss_bytes) as f64;
        1.0 - (1.0 - self.loss_prob_per_segment).powf(segments)
    }

    /// A configuration that fires no envelopes: cold/idle envelopes have unit
    /// depth and zero release, loss probability is zero.
    pub fn disabled() -> Self {
        Self {
            mss_bytes: 1460,
            initial_cwnd_segments: 10,
            idle_reset_threshold: Duration::MAX,
            rto: Duration::ZERO,
            loss_prob_per_segment: 0.0,
            loss_bw_depth: 1.0,
            cold_bw_depth: 1.0,
            cold_release: Duration::ZERO,
            cold_release_shape: Curve::Step,
            loss_release: Duration::ZERO,
            loss_release_shape: Curve::Step,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defaults_for_typical_long_haul_link() {
        let cfg = LinkEnvelopeCfg::defaults_for(Duration::from_millis(150), 1_000_000);
        // BDP = 150_000 bytes; IW = 14_600 bytes; depth ≈ 14600/300000.
        assert!((cfg.cold_bw_depth - 14_600.0 / 300_000.0).abs() < 1e-9);
        // log2(300000/14600) ≈ 4.36 RTTs × 300ms ≈ 1.308s.
        let expected = (300_000.0_f64 / 14_600.0).log2() * 0.3;
        assert!((cfg.cold_release.as_secs_f64() - expected).abs() < 1e-6);
        assert_eq!(cfg.idle_reset_threshold, Duration::from_secs(1));
        assert_eq!(cfg.rto, Duration::from_secs(1));
    }

    #[test]
    fn fast_link_skips_slow_start() {
        // 1 ms latency, 1 Gbps → BDP = 125_000 bytes, 2·BDP = 250_000; IW = 14_600.
        // 2·BDP > IW, so slow-start still applies. Use a degenerate case instead.
        let cfg = LinkEnvelopeCfg::defaults_for(Duration::from_micros(1), 1_000_000);
        assert_eq!(cfg.cold_bw_depth, 1.0);
        assert_eq!(cfg.cold_release, Duration::ZERO);
    }

    #[test]
    fn disabled_has_no_effect_parameters() {
        let cfg = LinkEnvelopeCfg::disabled();
        assert_eq!(cfg.cold_bw_depth, 1.0);
        assert_eq!(cfg.loss_prob_per_segment, 0.0);
        assert_eq!(cfg.idle_reset_threshold, Duration::MAX);
    }

    #[test]
    fn msg_loss_prob_scales_with_segment_count() {
        let mut cfg = LinkEnvelopeCfg::defaults_for(Duration::from_millis(100), 1_000_000);
        cfg.loss_prob_per_segment = 0.001;
        // Single-segment message: p_msg ≈ p_seg.
        assert!((cfg.msg_loss_prob(1000) - 0.001).abs() < 1e-9);
        // Ten-segment message: 1 - (1 - 0.001)^10 ≈ 0.00996.
        assert!((cfg.msg_loss_prob(10 * cfg.mss_bytes) - 0.009955_f64).abs() < 1e-5);
    }

    #[test]
    fn msg_loss_prob_zero_when_disabled() {
        let cfg = LinkEnvelopeCfg::disabled();
        assert_eq!(cfg.msg_loss_prob(1_000_000), 0.0);
    }
}
