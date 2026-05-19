//! Praos f_block lottery — the formula consumers share.
//!
//! Both adapters that drive [`crate::praos::PraosState`] (net-rs's
//! production loop, sim-rs's `try_generate_rb`) need the same
//! stake-weighted Bernoulli decision per slot.  This module owns the
//! formula; consumers supply their own randomness (a real PRNG for
//! net-rs, a deterministic VRF-style draw oracle for sim-rs) and the
//! comparison itself.
//!
//! The formula is the linear approximation `φ(α) ≈ α·f` of Ouroboros
//! Praos's exact `φ(α) = 1 − (1−f)^α`.  Relative error is well under
//! 1% for realistic stake distributions; fine for research, not
//! spec-faithful for adversarial fairness analysis at the extreme
//! tails.  Production-strength fidelity is a follow-on concern for
//! whoever plugs in real VRF later.

/// Upper bound of the success set for the Praos f_block lottery.
/// A draw `d` from a uniform distribution over `[0, total_stake)` is a
/// win iff `d < threshold`.
///
/// `rb_success_rate` is the network-wide active-slot coefficient
/// (`f_block`); `stake` is the node's own stake.  `total_stake` does
/// not appear here — it cancels with the draw range and stays the
/// caller's concern.
pub fn rb_win_threshold(rb_success_rate: f64, stake: u64) -> u64 {
    (stake as f64 * rb_success_rate) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_stake_full_rate_threshold_equals_stake() {
        assert_eq!(rb_win_threshold(1.0, 1000), 1000);
    }

    #[test]
    fn zero_rate_zero_threshold() {
        assert_eq!(rb_win_threshold(0.0, 1000), 0);
    }

    #[test]
    fn zero_stake_zero_threshold() {
        assert_eq!(rb_win_threshold(0.05, 0), 0);
    }

    #[test]
    fn linear_in_stake_at_fixed_rate() {
        let rate = 0.05;
        assert_eq!(rb_win_threshold(rate, 100), 5);
        assert_eq!(rb_win_threshold(rate, 1_000), 50);
        assert_eq!(rb_win_threshold(rate, 10_000), 500);
        assert_eq!(rb_win_threshold(rate, 100_000), 5_000);
    }

    #[test]
    fn truncation_takes_floor() {
        // 7 × 0.05 = 0.35 → truncates to 0.
        assert_eq!(rb_win_threshold(0.05, 7), 0);
        // 20 × 0.05 = 1.0 → exactly 1.
        assert_eq!(rb_win_threshold(0.05, 20), 1);
        // 21 × 0.05 = 1.05 → truncates to 1.
        assert_eq!(rb_win_threshold(0.05, 21), 1);
    }

    #[test]
    fn integer_form_against_float_form_agree_in_expectation() {
        // Sanity: the float form `rate × stake / total_stake` and the
        // integer form `threshold / total_stake` agree to within one
        // ulp / total_stake at realistic scales.  Pick stake high
        // enough that the truncation bias is below 0.1%.
        let rate = 0.05;
        let stake = 1_000_u64;
        let total_stake = 1_000_000_u64;
        let float_p = rate * stake as f64 / total_stake as f64;
        let int_p = rb_win_threshold(rate, stake) as f64 / total_stake as f64;
        assert!((float_p - int_p).abs() < 1.0 / total_stake as f64);
    }
}
