use crate::{step_function::PairIterators, CompactionMode, StepFunction, StepFunctionError};
use itertools::Itertools;
use std::{fmt, str::FromStr};

#[derive(Debug, PartialEq)]
pub enum CDFError {
    InvalidDataRange,
    NonMonotonicData,
    InvalidFraction,
    InvalidFormat(&'static str, usize),
}

impl fmt::Display for CDFError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CDFError::InvalidDataRange => {
                write!(f, "Data vector must contain values between 0 and 1")
            }
            CDFError::NonMonotonicData => write!(
                f,
                "Data vector must contain monotonically increasing values"
            ),
            CDFError::InvalidFraction => write!(f, "Fraction must be between 0 and 1"),
            CDFError::InvalidFormat(s, pos) => write!(f, "Invalid format: {s} at {pos}"),
        }
    }
}

impl std::error::Error for CDFError {}

impl From<StepFunctionError> for CDFError {
    fn from(err: StepFunctionError) -> Self {
        match err {
            StepFunctionError::InvalidFormat(s, p) => CDFError::InvalidFormat(s, p),
            StepFunctionError::InvalidDataRange => CDFError::InvalidDataRange,
            StepFunctionError::NonMonotonicData => CDFError::NonMonotonicData,
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
    /// Create a new CDF from a vector of data and a bin size.
    /// The data vector must contain values between 0 and 1, and must be
    /// monotonically increasing.
    pub fn new(data: &[f32], bin_size: f32) -> Result<Self, CDFError> {
        if !data.iter().all(|&y| y >= 0.0 && y <= 1.0) {
            return Err(CDFError::InvalidDataRange);
        }
        if !data.windows(2).all(|w| w[0] <= w[1]) {
            return Err(CDFError::NonMonotonicData);
        }
        let mut prev = 0.0;
        Ok(Self {
            steps: StepFunction::new(
                &data
                    .iter()
                    .enumerate()
                    .map(|(i, &x)| (i as f32 * bin_size, x))
                    .filter(|&(_, y)| {
                        let ret = y > prev;
                        prev = y;
                        ret
                    })
                    .collect::<Vec<_>>(),
            )?,
        })
    }

    /// Create a CDF from a step function.
    ///
    /// This validates that the y-values are in the range (0, 1] and are strictly monotonically increasing.
    pub fn from_step_function(steps: StepFunction) -> Result<Self, CDFError> {
        if !steps.iter().all(|(_x, y)| y > 0.0 && y <= 1.0) {
            return Err(CDFError::InvalidDataRange);
        }
        if !steps
            .iter()
            .tuple_windows::<(_, _)>()
            .all(|(a, b)| a.1 < b.1)
        {
            return Err(CDFError::NonMonotonicData);
        }
        Ok(Self { steps })
    }

    /// Create a step function CDF from a vector of (x, y) pairs.
    /// The x values must be greater than 0 and must be strictly monotonically increasing.
    /// The y values must be from (0, 1] and must be strictly monotonically increasing.
    pub fn from_steps(data: &[(f32, f32)]) -> Result<Self, CDFError> {
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
            return Err(CDFError::InvalidFraction);
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
        let steps = self.steps.compact(data)?;
        Ok(CDF { steps })
    }

    /// Combine two CDFs by universal quantification, meaning that both outcomes must occur.
    pub fn for_all(&self, other: &CDF) -> Result<CDF, CDFError> {
        let mut data = Vec::new();
        for (x, (ly, ry)) in self.steps.zip(&other.steps) {
            let y = ly * ry;
            data.push((x, y));
        }
        let steps = self.steps.compact(data)?;
        Ok(CDF { steps })
    }

    /// Combine two CDFs by existential quantification, meaning that at least one of the outcomes
    pub fn for_some(&self, other: &CDF) -> Result<CDF, CDFError> {
        let mut data = Vec::new();
        for (x, (ly, ry)) in self.steps.zip(&other.steps) {
            let y = (ly + ry - ly * ry).clamp(0.0, 1.0);
            data.push((x, y));
        }
        let steps = self.steps.compact(data)?;
        Ok(CDF { steps })
    }

    /// Convolve two CDFs, which is equivalent to taking the sum of all possible outcomes of the
    /// two CDFs. This describes the distribution of the sum of two independent random variables.
    pub fn convolve(&self, other: &CDF) -> Result<CDF, CDFError> {
        let steps = self.convolve_step(&other.steps, 1.0)?;
        Ok(CDF { steps })
    }

    /// Convolve a CDF with a step function, which means smearing out the step function by the
    /// gradual completion of the CDF.
    pub fn convolve_step(
        &self,
        other: &StepFunction,
        max: f32,
    ) -> Result<StepFunction, StepFunctionError> {
        // start with the all-zero CDF
        let mut data = Vec::new();
        let mut prev_y = 0.0;
        for (lx, ly) in self.steps.iter() {
            let step = ly - prev_y;
            // take the other CDF, scale it by the step size, shift it by the current x value, and add it into the data
            let mut d = Vec::new();
            let iter = PairIterators::new(
                data.iter().copied(),
                other.iter().map(|(x, y)| (x + lx, y * step)),
            );
            for (x, (ly, ry)) in iter {
                d.push((x, (ly + ry).min(max)));
            }
            data = d;
            prev_y = ly;
        }
        let steps = self.steps.compact(data)?;
        Ok(steps)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        CDF::new(&[0.0, 0.25, 0.5, 0.75, 1.0], 0.25).unwrap();

        let cdf = CDF::new(&[0.0, 0.25, 0.5, 0.75, 1.1], 0.25);
        assert_eq!(cdf, Err(CDFError::InvalidDataRange));

        let cdf = CDF::new(&[0.0, 0.25, 0.5, 0.75, 0.5], 0.25);
        assert_eq!(cdf, Err(CDFError::NonMonotonicData));
    }

    #[test]
    fn test_choice() {
        let left = CDF::new(&[0.0, 0.0, 0.5, 1.0, 1.0], 0.25).unwrap();
        let right = CDF::new(&[0.0, 1.0, 1.0, 1.0, 1.0], 0.25).unwrap();
        let added = left.choice(0.7, &right).unwrap();
        assert_eq!(added, CDF::new(&[0.0, 0.3, 0.65, 1.0, 1.0], 0.25).unwrap());
        let added = left.choice(1.0, &right).unwrap();
        assert_eq!(added, CDF::new(&[0.0, 0.0, 0.5, 1.0, 1.0], 0.25).unwrap());
    }

    #[test]
    fn test_convolve_step() {
        let left = CDF::new(&[0.0, 1.0, 1.0, 1.0, 1.0], 1.0).unwrap();
        let right = CDF::new(&[0.0, 0.0, 1.0, 1.0, 1.0], 1.0).unwrap();
        let convolved = left.convolve(&right).unwrap();
        assert_eq!(
            convolved,
            CDF::new(&[0.0, 0.0, 0.0, 1.0, 1.0], 1.0).unwrap()
        );
    }

    #[test]
    fn test_convolve_two() {
        let left = CDF::new(&[0.0, 0.3, 0.3, 1.0, 1.0, 1.0, 1.0], 1.0).unwrap();
        let right = CDF::new(&[0.0, 0.0, 0.6, 1.0, 1.0, 1.0, 1.0], 1.0).unwrap();
        let convolved = left.convolve(&right).unwrap();
        assert_eq!(
            convolved,
            CDF::new(&[0.0, 0.0, 0.0, 0.18, 0.3, 0.72, 1.0], 1.0).unwrap()
        );
    }

    #[test]
    fn test_for_all() {
        let left = CDF::new(&[0.0, 0.5, 0.75, 1.0], 0.25).unwrap();
        let right = CDF::new(&[0.0, 0.25, 0.5, 1.0], 0.25).unwrap();
        let result = left.for_all(&right).unwrap();
        assert_eq!(result, CDF::new(&[0.0, 0.125, 0.375, 1.0], 0.25).unwrap());
    }

    #[test]
    fn test_for_some() {
        let left = CDF::new(&[0.0, 0.5, 0.75, 1.0], 0.25).unwrap();
        let right = CDF::new(&[0.0, 0.25, 0.5, 1.0], 0.25).unwrap();
        let result = left.for_some(&right).unwrap();
        assert_eq!(result, CDF::new(&[0.0, 0.625, 0.875, 1.0], 0.25).unwrap());
    }

    #[test]
    fn partial_ord() {
        let left = CDF::new(&[0.0, 0.3, 0.3, 1.0], 1.0).unwrap();
        let right = CDF::new(&[0.0, 0.0, 0.6, 1.0], 1.0).unwrap();
        let top = CDF::new(&[0.0, 0.3, 0.6, 1.0], 1.0).unwrap();
        let bottom = CDF::new(&[0.0, 0.0, 0.3, 1.0], 1.0).unwrap();
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
        let cdf = CDF::new(&[0.1, 0.25, 0.5, 0.75, 1.0], 0.25).unwrap();
        assert_eq!(
            format!("{}", cdf),
            "CDF[(0, 0.1), (0.25, 0.25), (0.5, 0.5), (0.75, 0.75), (1, 1)]"
        );
    }

    #[test]
    fn test_from_str() {
        let cdf_str = "CDF[(0, 0.1), (0.25, 0.25), (0.5, 0.5), (0.75, 0.75), (1, 1)]";
        let cdf: CDF = cdf_str.parse().unwrap();
        assert_eq!(cdf, CDF::new(&[0.1, 0.25, 0.5, 0.75, 1.0], 0.25).unwrap());

        let invalid_cdf_str = "CDF[(0, 0), (0.25, 0.25), (0.5, 0.5), (0.75, 0.75), (1, 1.1)]";
        let cdf: Result<CDF, CDFError> = invalid_cdf_str.parse();
        assert_eq!(cdf, Err(CDFError::InvalidDataRange));

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
