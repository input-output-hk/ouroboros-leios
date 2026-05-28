//! Praos f_block lottery — the formula consumers share.
//!
//! Both adapters that drive [`crate::praos::PraosState`] (net-rs's
//! production loop, sim-rs's `try_generate_rb`) need the same
//! stake-weighted Bernoulli decision per slot.  This module owns the
//! formula; consumers supply their own randomness (a real PRNG for
//! net-rs, a deterministic VRF-style draw oracle for sim-rs) and the
//! comparison itself.
//!
//! The formula is the spec-faithful Ouroboros Praos lottery
//! probability `φ(σ) = 1 − (1 − f)^σ`, where `σ = stake / total_stake`
//! and `f` is the network-wide active-slot coefficient.  The threshold
//! is returned as a `u64` over the half-open range `[0, 2^64)`; a
//! uniform integer draw `d` wins iff `d < threshold`.  The integer
//! comparison shape matches what a real VRF check will use — when a
//! VRF lands, only the draw source changes.
//!
//! Internally the threshold is computed in `f64` and quantized.  Float
//! precision is well below the `1 / 2^64` resolution of the comparison
//! for any realistic `(f, σ)`, so the quantization step is the only
//! place precision is lost.  The internal evaluation uses `exp_m1` to
//! avoid catastrophic cancellation when `φ` is small (the common case
//! for low-stake nodes).

/// Per-epoch lottery context.
///
/// Holds `ln(1 − f)` precomputed once so per-slot threshold evaluation
/// is a single `exp_m1` and a quantization.
#[derive(Debug, Clone, Copy)]
pub struct LotteryParams {
    /// `ln(1 − f)`.  Always non-positive.  Set to `f64::NEG_INFINITY`
    /// when `f == 1.0`, in which case every non-zero-stake threshold
    /// saturates at `u64::MAX`.
    ln_one_minus_f: f64,
}

impl LotteryParams {
    /// `f` is the active-slot coefficient.  Must lie in `[0.0, 1.0]`.
    pub fn new(f: f64) -> Self {
        assert!(
            (0.0..=1.0).contains(&f),
            "active-slot coefficient f must lie in [0,1]; got {f}"
        );
        Self {
            ln_one_minus_f: (1.0 - f).ln(),
        }
    }

    /// Threshold over `[0, 2^64)` for the Praos f_block lottery: a
    /// uniform draw `d` wins iff `d < threshold`.
    ///
    /// `stake / total_stake` may exceed 1 only through caller bug; the
    /// math is still well-defined and saturates at `u64::MAX`.
    pub fn rb_win_threshold(&self, stake: u64, total_stake: u64) -> u64 {
        if stake == 0 || total_stake == 0 {
            return 0;
        }
        let sigma = stake as f64 / total_stake as f64;
        // φ(σ) = 1 − (1 − f)^σ = 1 − exp(σ · ln(1 − f)) = −expm1(σ · ln(1 − f)).
        // `exp_m1` keeps full f64 precision when its argument is near 0,
        // which is the small-σ regime; computing `1 - exp(x)` directly
        // would cancel away most of the bits there.
        let phi = -(sigma * self.ln_one_minus_f).exp_m1();
        quantize_phi(phi)
    }
}

/// Map a probability `φ ∈ [0, 1]` to the `[0, 2^64)` integer range.
/// Saturates at `u64::MAX` for `φ ≥ 1`; returns 0 for `φ ≤ 0`.
fn quantize_phi(phi: f64) -> u64 {
    // `2^64` is exactly representable in f64 (it's a power of two and
    // fits in the exponent), but it doesn't fit in u64 — anything that
    // would round up to `2^64` must saturate.
    const TWO_POW_64: f64 = 18446744073709551616.0;
    if !phi.is_finite() || phi <= 0.0 {
        return 0;
    }
    if phi >= 1.0 {
        return u64::MAX;
    }
    let scaled = phi * TWO_POW_64;
    if scaled >= TWO_POW_64 {
        u64::MAX
    } else {
        scaled as u64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TWO_POW_64: f64 = 18446744073709551616.0;

    fn rate(params: &LotteryParams, stake: u64, total_stake: u64) -> f64 {
        params.rb_win_threshold(stake, total_stake) as f64 / TWO_POW_64
    }

    #[test]
    fn zero_f_zero_threshold() {
        let p = LotteryParams::new(0.0);
        assert_eq!(p.rb_win_threshold(1000, 1000), 0);
    }

    #[test]
    fn zero_stake_zero_threshold() {
        let p = LotteryParams::new(0.05);
        assert_eq!(p.rb_win_threshold(0, 1000), 0);
    }

    #[test]
    fn zero_total_stake_zero_threshold() {
        let p = LotteryParams::new(0.05);
        assert_eq!(p.rb_win_threshold(1, 0), 0);
    }

    #[test]
    fn full_f_full_stake_saturates() {
        let p = LotteryParams::new(1.0);
        assert_eq!(p.rb_win_threshold(1, 1), u64::MAX);
    }

    #[test]
    fn full_stake_yields_f() {
        // σ = 1 ⇒ φ(1) = 1 − (1 − f) = f.
        let p = LotteryParams::new(0.05);
        let observed = rate(&p, 1000, 1000);
        assert!((observed - 0.05).abs() < 1e-15, "observed = {observed}");
    }

    #[test]
    fn tiny_stake_has_nonzero_threshold() {
        // The bug that prompted this rewrite: previously `stake × f < 1`
        // truncated the threshold to zero, locking the node out of the
        // lottery forever.  Spec-faithful φ is strictly positive for any
        // non-zero stake at non-zero f.
        let p = LotteryParams::new(0.05);
        // 100-node cluster, equal stake: 10/1000 with f=0.05.
        assert!(p.rb_win_threshold(10, 1000) > 0);
        // Even a single stake unit out of a million still wins eventually.
        assert!(p.rb_win_threshold(1, 1_000_000) > 0);
    }

    #[test]
    fn first_derivative_at_zero_matches_neg_ln_one_minus_f() {
        // φ'(0) = −ln(1 − f).  Verify by checking that for σ → 0 the
        // rate φ/σ converges to that constant.
        let f = 0.05;
        let p = LotteryParams::new(f);
        let expected_slope = -(1.0_f64 - f).ln();
        // Pick σ small enough that the second-order term σ·f²/2 is below
        // the assertion tolerance.
        for (stake, total_stake) in [(1u64, 10_000_000u64), (1, 100_000_000)] {
            let sigma = stake as f64 / total_stake as f64;
            let observed_slope = rate(&p, stake, total_stake) / sigma;
            assert!(
                (observed_slope - expected_slope).abs() < 1e-8,
                "σ={sigma}: φ/σ={observed_slope}, expected ≈ {expected_slope}"
            );
        }
    }

    #[test]
    fn matches_libm_powf_reference() {
        // Cross-check against the direct `(1-f).powf(σ)` form for a few
        // points.  Catches any drift in the expm1-based path.
        let f = 0.05;
        let p = LotteryParams::new(f);
        for (stake, total_stake) in [(1u64, 1_000_000u64), (10, 1_000), (500, 1_000), (1, 1)] {
            let sigma = stake as f64 / total_stake as f64;
            let reference = 1.0 - (1.0_f64 - f).powf(sigma);
            let observed = rate(&p, stake, total_stake);
            assert!(
                (observed - reference).abs() < 1e-15_f64.max(reference * 1e-12),
                "σ={sigma}: observed={observed}, reference={reference}"
            );
        }
    }

    #[test]
    fn monotone_in_stake() {
        let p = LotteryParams::new(0.05);
        let mut prev = 0;
        for stake in [1u64, 10, 100, 1_000, 10_000, 100_000, 1_000_000] {
            let t = p.rb_win_threshold(stake, 1_000_000);
            assert!(t > prev, "stake={stake}: threshold {t} not > prev {prev}");
            prev = t;
        }
    }

    #[test]
    fn empirical_rate_matches_phi() {
        // Monte Carlo: draw 100k u64s with a seeded PRNG; observed win
        // rate should be within 4σ of φ.  At n=100k, p≈0.05, 4σ ≈ 4·√(np(1−p))
        // ≈ 275 wins, i.e. < 0.3% deviation.
        use rand::{Rng, SeedableRng};
        let f = 0.05;
        let stake = 100u64;
        let total_stake = 1_000u64;
        let p = LotteryParams::new(f);
        let threshold = p.rb_win_threshold(stake, total_stake);
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xc4f1_7d05_u64);
        let n = 100_000;
        let wins = (0..n).filter(|_| rng.gen::<u64>() < threshold).count();
        let observed = wins as f64 / n as f64;
        let expected = 1.0 - (1.0 - f).powf(stake as f64 / total_stake as f64);
        let stderr = (expected * (1.0 - expected) / n as f64).sqrt();
        assert!(
            (observed - expected).abs() < 4.0 * stderr,
            "observed {observed}, expected {expected} ± {}",
            4.0 * stderr
        );
    }
}
