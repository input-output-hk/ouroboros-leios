use rand_distr::{Distribution, Exp, Normal};

#[derive(Debug, Clone, Copy)]
pub enum FloatDistribution {
    Normal(Normal<f64>),
    ScaledExp(Exp<f64>, f64),
}
impl FloatDistribution {
    pub fn normal(mean: f64, std_dev: f64) -> Self {
        Self::Normal(Normal::new(mean, std_dev).unwrap())
    }
    pub fn scaled_exp(lambda: f64, scale: f64) -> Self {
        Self::ScaledExp(Exp::new(lambda).unwrap(), scale)
    }
}

impl Distribution<f64> for FloatDistribution {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> f64 {
        match self {
            Self::Normal(d) => d.sample(rng),
            Self::ScaledExp(d, scale) => d.sample(rng) * scale,
        }
    }
}
