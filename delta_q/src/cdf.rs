use crate::{CompactionMode, StepFunction, StepFunctionError, StepValue, DEFAULT_MAX_SIZE};
use itertools::Itertools;
use std::{fmt, str::FromStr, sync::OnceLock};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CDFError {
    InvalidDataRange(&'static str, f32),
    NonMonotonicData,
    InvalidFraction(f32),
    InvalidFormat(&'static str, usize),
    ProbabilityOverflow(f32),
}

impl fmt::Display for CDFError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CDFError::InvalidDataRange(s, y) => {
                write!(
                    f,
                    "Data vector must contain values between 0 and 1, found {s}={y}"
                )
            }
            CDFError::NonMonotonicData => write!(
                f,
                "Data vector must contain monotonically increasing values"
            ),
            CDFError::InvalidFraction(y) => write!(f, "Fraction must be between 0 and 1: {y}"),
            CDFError::InvalidFormat(s, pos) => write!(f, "Invalid format: {s} at {pos}"),
            CDFError::ProbabilityOverflow(y) => write!(f, "Probability overflow: {y}"),
        }
    }
}

impl std::error::Error for CDFError {}

impl From<StepFunctionError> for CDFError {
    fn from(err: StepFunctionError) -> Self {
        match err {
            StepFunctionError::InvalidFormat(s, p) => CDFError::InvalidFormat(s, p),
            StepFunctionError::InvalidDataRange(s, y) => CDFError::InvalidDataRange(s, y),
            StepFunctionError::NonMonotonicData => CDFError::NonMonotonicData,
            StepFunctionError::InvalidFraction(y) => CDFError::InvalidFraction(y),
            StepFunctionError::ProbabilityOverflow(y) => CDFError::ProbabilityOverflow(y),
        }
    }
}

/// A Cumulative Distribution Function (CDF) is a representation of a probability
/// distribution that can be manipulated in various ways.
#[derive(Debug, Clone, PartialEq, PartialOrd, serde::Serialize, serde::Deserialize)]
pub struct CDF {
    /// invariants: y-values are in the range (0, 1] and must be strictly monotonically increasing
    steps: StepFunction,
}

impl Default for CDF {
    fn default() -> Self {
        Self::top()
    }
}

impl fmt::Display for CDF {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CDF")?;
        write!(f, "{}", self.steps)?;
        Ok(())
    }
}

impl FromStr for CDF {
    type Err = CDFError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let steps = s.trim_start_matches("CDF").parse()?;
        Self::from_step_function(steps)
    }
}

impl CDF {
    pub fn top() -> Self {
        static TOP: OnceLock<CDF> = OnceLock::new();
        TOP.get_or_init(|| Self::new(&[(0.0, 1.0)]).unwrap())
            .clone()
    }

    pub fn bottom() -> Self {
        static BOTTOM: OnceLock<CDF> = OnceLock::new();
        BOTTOM
            .get_or_init(|| Self {
                steps: StepFunction::zero(),
            })
            .clone()
    }

    /// Create a CDF from a step function.
    ///
    /// This validates that the y-values are in the range (0, 1] and are strictly monotonically increasing.
    pub fn from_step_function(steps: StepFunction) -> Result<Self, CDFError> {
        for (_, y) in steps.iter() {
            if y <= 0.0 || y > 1.0 {
                return Err(CDFError::InvalidDataRange("y", y));
            }
        }
        if !steps
            .iter()
            .tuple_windows::<(_, _)>()
            .all(|(a, b)| a.1 < b.1)
        {
            #[cfg(target_arch = "wasm32")]
            web_sys::console::error_2(&"non-monotonic".into(), &format!("{}", steps).into());
            return Err(CDFError::NonMonotonicData);
        }
        Ok(Self { steps })
    }

    pub fn from_step_at(step: f32) -> Self {
        Self::new(&[(step, 1.0)]).unwrap()
    }

    /// Create a step function CDF from a vector of (x, y) pairs.
    /// The x values must be greater than 0 and must be strictly monotonically increasing.
    /// The y values must be from (0, 1] and must be strictly monotonically increasing.
    pub fn new(data: &[(f32, f32)]) -> Result<Self, CDFError> {
        Self::from_step_function(StepFunction::new(data)?)
    }

    /// Set the maximum size of the CDF using a mutable reference.
    pub fn set_max_size(&mut self, max_size: usize) {
        self.steps.set_max_size(max_size);
    }

    /// Set the compaction mode of the CDF using a mutable reference.
    pub fn set_mode(&mut self, mode: CompactionMode) {
        self.steps.set_mode(mode);
    }

    /// Set the maximum size of the CDF using builder pattern.
    pub fn with_max_size(mut self, max_size: usize) -> Self {
        self.steps.set_max_size(max_size);
        self
    }

    /// Set the compaction mode of the CDF using builder pattern.
    pub fn with_mode(mut self, mode: CompactionMode) -> Self {
        self.steps.set_mode(mode);
        self
    }

    pub fn iter(&self) -> impl Iterator<Item = (f32, f32)> + '_ {
        self.steps.iter()
    }

    pub fn graph_iter(&self) -> impl Iterator<Item = (f32, f32)> + '_ {
        self.steps.graph_iter()
    }

    /// Get the width of the CDF.
    pub fn width(&self) -> f32 {
        self.steps.max_x()
    }

    pub fn steps(&self) -> &StepFunction {
        &self.steps
    }

    /// Combine two CDFs by choosing between them, using the given fraction as the probability for
    /// the first CDF.
    pub fn choice(&self, my_fraction: f32, other: &CDF) -> Result<CDF, CDFError> {
        if my_fraction < 0.0 || my_fraction > 1.0 {
            return Err(CDFError::InvalidFraction(my_fraction));
        }
        let fraction = 1.0 - my_fraction;
        let mut data = Vec::new();
        let mut prev_y = 0.0;
        for (x, (ly, ry)) in self.steps.zip(&other.steps) {
            let y = (ly * my_fraction + ry * fraction).min(1.0);
            if y > prev_y {
                prev_y = y;
                data.push((x, y));
            }
        }
        f32::compact(&mut data, self.steps.mode(), self.steps.max_size());
        Ok(CDF {
            steps: StepFunction::try_from(data)?
                .with_mode(self.steps.mode())
                .with_max_size(self.steps.max_size()),
        })
    }

    /// Combine two CDFs by universal quantification, meaning that both outcomes must occur.
    pub fn for_all(&self, other: &CDF) -> CDF {
        let mut data = Vec::new();
        for (x, (ly, ry)) in self.steps.zip(&other.steps) {
            let y = ly * ry;
            data.push((x, y));
        }
        f32::compact(&mut data, self.steps.mode(), self.steps.max_size());
        CDF {
            steps: StepFunction::try_from(data)
                .expect("step function error")
                .with_mode(self.steps.mode())
                .with_max_size(self.steps.max_size()),
        }
    }

    /// Combine two CDFs by existential quantification, meaning that at least one of the outcomes
    pub fn for_some(&self, other: &CDF) -> CDF {
        let mut data = Vec::new();
        for (x, (ly, ry)) in self.steps.zip(&other.steps) {
            let y = (ly + ry - ly * ry).clamp(0.0, 1.0);
            data.push((x, y));
        }
        f32::compact(&mut data, self.steps.mode(), self.steps.max_size());
        CDF {
            steps: StepFunction::try_from(data)
                .expect("step function error")
                .with_mode(self.steps.mode())
                .with_max_size(self.steps.max_size()),
        }
    }

    /// Convolve two CDFs, which is equivalent to taking the sum of all possible outcomes of the
    /// two CDFs. This describes the distribution of the sum of two independent random variables.
    pub fn convolve(&self, other: &CDF) -> CDF {
        let steps = self.convolve_step(&other.steps);
        CDF { steps }
    }

    /// Convolve a CDF with a step function, which means smearing out the step function by the
    /// gradual completion of the CDF.
    pub fn convolve_step<T: StepValue>(&self, other: &StepFunction<T>) -> StepFunction<T> {
        // start with the all-zero CDF
        let mut data = Vec::new();
        let mut prev_y = 0.0;
        let zero_prob = T::add_prob_zero();
        let zero_sum = T::sum_up_zero();
        for (lx, ly) in self.steps.iter() {
            let step = ly - prev_y;
            // take the other CDF, scale it by the step size, shift it by the current x value, and add it into the data
            let mut d = Vec::new();
            let iter = crate::step_function::zip(
                data.iter().map(|(x, y)| (*x, y)),
                other.iter().map(|(x, y)| (x + lx, y.scale_prob(step))),
                &zero_prob,
                zero_sum.scale_prob(step),
            );
            for (x, (ly, ry)) in iter {
                d.push((x, ly.add_prob(&ry).expect("probability overflow")));
            }
            data = d;
            prev_y = ly;
        }
        T::compact(&mut data, self.steps.mode(), self.steps.max_size());
        StepFunction::try_from(data)
            .expect("step function error")
            .with_mode(self.steps.mode())
            .with_max_size(self.steps.max_size())
    }
}

impl FromIterator<(f32, f32)> for CDF {
    fn from_iter<I: IntoIterator<Item = (f32, f32)>>(iter: I) -> Self {
        let mut data = iter.into_iter().collect::<Vec<_>>();
        f32::compact(&mut data, CompactionMode::default(), DEFAULT_MAX_SIZE);
        Self::new(&data).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        CDF::new(&[(0.25, 0.25), (0.5, 0.5), (0.75, 0.75), (1.0, 1.0)]).unwrap();

        let cdf = CDF::new(&[(0.25, 0.25), (0.5, 0.5), (0.75, 0.75), (1.0, 1.1)]);
        assert_eq!(cdf, Err(CDFError::InvalidDataRange("y", 1.1)));

        let cdf = CDF::new(&[(0.25, 0.25), (0.5, 0.5), (0.75, 0.75), (1.0, 0.5)]);
        assert_eq!(cdf, Err(CDFError::NonMonotonicData));
    }

    #[test]
    fn test_choice() {
        let left = CDF::new(&[(0.5, 0.5), (0.75, 1.0)]).unwrap();
        let right = CDF::new(&[(0.25, 1.0)]).unwrap();
        let added = left.choice(0.7, &right).unwrap();
        assert_eq!(
            added,
            CDF::new(&[(0.25, 0.3), (0.5, 0.65), (0.75, 1.0)]).unwrap()
        );
        let added = left.choice(1.0, &right).unwrap();
        assert_eq!(added, CDF::new(&[(0.5, 0.5), (0.75, 1.0)]).unwrap());
    }

    #[test]
    fn test_convolve_step() {
        let left = CDF::new(&[(1.0, 1.0)]).unwrap();
        let right = CDF::new(&[(2.0, 1.0)]).unwrap();
        let convolved = left.convolve(&right);
        assert_eq!(convolved, CDF::new(&[(3.0, 1.0)]).unwrap());
    }

    #[test]
    fn test_convolve_two() {
        let left = CDF::new(&[(1.0, 0.3), (3.0, 1.0)]).unwrap();
        let right = CDF::new(&[(2.0, 0.6), (3.0, 1.0)]).unwrap();
        let convolved = left.convolve(&right);
        assert_eq!(
            convolved,
            CDF::new(&[(3.0, 0.18), (4.0, 0.3), (5.0, 0.72), (6.0, 1.0)]).unwrap()
        );
    }

    #[test]
    fn test_for_all() {
        let left = CDF::new(&[(0.25, 0.5), (0.5, 0.75), (0.75, 1.0)]).unwrap();
        let right = CDF::new(&[(0.25, 0.25), (0.5, 0.5), (0.75, 1.0)]).unwrap();
        let result = left.for_all(&right);
        assert_eq!(
            result,
            CDF::new(&[(0.25, 0.125), (0.5, 0.375), (0.75, 1.0)]).unwrap()
        );
    }

    #[test]
    fn test_for_some() {
        let left = CDF::new(&[(0.25, 0.5), (0.5, 0.75), (0.75, 1.0)]).unwrap();
        let right = CDF::new(&[(0.25, 0.25), (0.5, 0.5), (0.75, 1.0)]).unwrap();
        let result = left.for_some(&right);
        assert_eq!(
            result,
            CDF::new(&[(0.25, 0.625), (0.5, 0.875), (0.75, 1.0)]).unwrap()
        );
    }

    #[test]
    fn partial_ord() {
        let left = CDF::new(&[(1.0, 0.3), (3.0, 1.0)]).unwrap();
        let right = CDF::new(&[(2.0, 0.6), (3.0, 1.0)]).unwrap();
        let top = CDF::new(&[(1.0, 0.3), (2.0, 0.6), (3.0, 1.0)]).unwrap();
        let bottom = CDF::new(&[(2.0, 0.3), (3.0, 1.0)]).unwrap();
        assert_ne!(left, right);
        assert!(!(left < right));
        assert!(!(right > left));
        assert!(!(left <= right));
        assert!(!(right >= left));
        assert!(left < top);
        assert!(top > left);
        assert!(left <= top);
        assert!(top >= left);
        assert!(right < top);
        assert!(top > right);
        assert!(right <= top);
        assert!(top >= right);
        assert!(left > bottom);
        assert!(bottom < left);
        assert!(left >= bottom);
        assert!(bottom <= left);
        assert!(right > bottom);
        assert!(bottom < right);
        assert!(right >= bottom);
        assert!(bottom <= right);
    }

    #[test]
    fn test_display() {
        let cdf = CDF::new(&[
            (0.0, 0.1),
            (0.25, 0.25),
            (0.5, 0.5),
            (0.75, 0.75),
            (1.0, 1.0),
        ])
        .unwrap();
        assert_eq!(
            format!("{}", cdf),
            "CDF[(0, 0.1), (0.25, 0.25), (0.5, 0.5), (0.75, 0.75), (1, 1)]"
        );
    }

    #[test]
    fn test_from_str() {
        let cdf_str = "CDF[(0, 0.1), (0.25, 0.25), (0.5, 0.5), (0.75, 0.75), (1, 1)]";
        let cdf: CDF = cdf_str.parse().unwrap();
        assert_eq!(
            cdf,
            CDF::new(&[
                (0.0, 0.1),
                (0.25, 0.25),
                (0.5, 0.5),
                (0.75, 0.75),
                (1.0, 1.0)
            ])
            .unwrap()
        );

        let invalid_cdf_str = "CDF[(0.25, 0.25), (0.5, 0.5), (0.75, 0.75), (1, 1.1)]";
        let cdf: Result<CDF, CDFError> = invalid_cdf_str.parse();
        assert_eq!(cdf, Err(CDFError::InvalidDataRange("y", 1.1)));

        let invalid_format_str = "CDF[(0, 0.1), (0.25, 0.25), (0.5, 0.5), (0.75, 0.75), 1, 1)]";
        let cdf: Result<CDF, CDFError> = invalid_format_str.parse();
        assert!(
            matches!(cdf, Err(CDFError::InvalidFormat(_, _))),
            "{:?}",
            cdf
        );

        let invalid_cdf_str = "CDF[(0, 0.1), (0.25, 0.25), (0.5, 0.25), (0.75, 0.75), (1, 1)";
        let cdf: Result<CDF, CDFError> = invalid_cdf_str.parse();
        assert_eq!(cdf, Err(CDFError::NonMonotonicData));

        let invalid_cdf_str = "CDF[(0, 0.1), (0.25, 0.25), (0.25, 0.5), (0.75, 0.75), (1, 1)";
        let cdf: Result<CDF, CDFError> = invalid_cdf_str.parse();
        assert_eq!(cdf, Err(CDFError::NonMonotonicData));
    }
}
