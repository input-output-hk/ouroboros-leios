use rand::Rng;
use rand_distr::{Distribution, Exp, LogNormal, Normal};
use std::fmt::Debug;

#[derive(Debug, Clone, Copy)]
pub enum FloatDistribution {
    Normal(Normal<f64>),
    ScaledExp(Exp<f64>, f64),
    LogNormal(LogNormal<f64>),
    Constant(Constant<f64>),
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
    pub fn constant(value: f64) -> Self {
        Self::Constant(Constant::new(value))
    }
}

impl Distribution<f64> for FloatDistribution {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> f64 {
        match self {
            Self::Normal(d) => d.sample(rng),
            Self::ScaledExp(d, scale) => d.sample(rng) * scale,
            Self::LogNormal(d) => d.sample(rng),
            Self::Constant(d) => d.sample(rng),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Constant<T>(T);
impl<T> Constant<T> {
    pub fn new(value: T) -> Self {
        Self(value)
    }
}

impl<T: Clone> Distribution<T> for Constant<T> {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> T {
        let _ = rng;
        self.0.clone()
    }
}
