use rand_distr::{Distribution, Exp, LogNormal, Normal};

#[derive(Debug, Clone, Copy)]
pub enum FloatDistribution {
    Normal(Normal<f64>),
    ScaledExp(Exp<f64>, f64),
    LogNormal(LogNormal<f64>),
}
impl FloatDistribution {
    pub fn normal(mean: f64, std_dev: f64) -> Self {
        Self::Normal(Normal::new(mean, std_dev).unwrap())
    }
    pub fn scaled_exp(lambda: f64, scale: f64) -> Self {
        Self::ScaledExp(Exp::new(lambda).unwrap(), scale)
    }
    pub fn log_normal(mu: f64, sigma: f64) -> Self {
        Self::LogNormal(LogNormal::new(mu, sigma).unwrap())
    }
}

impl Distribution<f64> for FloatDistribution {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> f64 {
        match self {
            Self::Normal(d) => d.sample(rng),
            Self::ScaledExp(d, scale) => d.sample(rng) * scale,
            Self::LogNormal(d) => d.sample(rng),
        }
    }
}
