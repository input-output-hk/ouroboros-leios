pub fn compute_target_vrf_stake(stake: u64, total_stake: u64, success_rate: f64) -> u64 {
    let ratio = stake as f64 / total_stake as f64;
    (total_stake as f64 * ratio * success_rate) as u64
}

pub fn vrf_probabilities(probability: f64) -> impl Iterator<Item = f64> {
    let final_success_rate = Some(probability.fract()).filter(|f| *f > 0.0);
    std::iter::repeat_n(1.0, probability.trunc() as usize).chain(final_success_rate)
}
