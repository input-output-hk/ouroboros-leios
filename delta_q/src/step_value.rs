use crate::{
    compaction::compact_cdf, step_function::zip, CDFError, CompactionMode, StepFunctionError, CDF,
};
use std::fmt::{self, Write as _};

pub trait StepValue: Clone + fmt::Debug {
    type Error: fmt::Debug;

    /// the zero to use with sum_up
    fn sum_up_zero() -> Self;
    /// the zero to use with add_prob
    fn add_prob_zero() -> Self;

    /// Add two values together so that the result means that both values are included
    fn sum_up(&self, other: &Self) -> Self;
    /// Add two values together probabilistically
    fn add_prob(&self, other: &Self, do_offset: bool) -> Result<Self, Self::Error>;
    /// Scale the probability density by a factor
    fn scale_prob(&self, factor: f32) -> Self;
    /// Combine two values by choosing one with a given probability
    fn choice(&self, my_fraction: f32, other: &Self) -> Result<Self, Self::Error>;
    fn compact(this: &mut Vec<(f32, Self)>, mode: CompactionMode, max_size: usize);
    fn similar(&self, other: &Self) -> bool;

    fn pretty_print(&self, f: &mut String) -> fmt::Result;
}

impl StepValue for f32 {
    type Error = StepFunctionError;

    fn sum_up_zero() -> Self {
        0.0
    }

    fn add_prob_zero() -> Self {
        0.0
    }

    fn sum_up(&self, other: &Self) -> Self {
        *self + *other
    }

    fn add_prob(&self, other: &Self, do_offset: bool) -> Result<Self, Self::Error> {
        let ret = *self + *other + if do_offset { -1.0 } else { 0.0 };
        if ret.similar(&1.0) {
            Ok(1.0)
        } else if ret > 1.0 {
            Err(StepFunctionError::ProbabilityOverflow(ret))
        } else if ret < 0.0 {
            Err(StepFunctionError::ProbabilityOverflow(ret))
        } else {
            Ok(ret)
        }
    }

    fn scale_prob(&self, factor: f32) -> Self {
        *self * factor
    }

    fn choice(&self, my_fraction: f32, other: &Self) -> Result<Self, Self::Error> {
        if my_fraction < 0.0 || my_fraction > 1.0 {
            return Err(StepFunctionError::InvalidFraction(my_fraction));
        }
        Ok(*self * my_fraction + *other * (1.0 - my_fraction))
    }

    fn compact(this: &mut Vec<(f32, Self)>, mode: CompactionMode, max_size: usize) {
        crate::compaction::compact(this, mode, max_size);
    }

    fn similar(&self, other: &Self) -> bool {
        *self == 0.0 && other.abs() < 1e-6
            || *other == 0.0 && self.abs() < 1e-6
            || (self - other).abs() / f32::max(*self, *other) < 1e-6
    }

    fn pretty_print(&self, f: &mut String) -> fmt::Result {
        write!(f, "{:.5}", self)
    }
}

impl StepValue for CDF {
    type Error = CDFError;

    fn sum_up_zero() -> Self {
        CDF::top()
    }

    fn add_prob_zero() -> Self {
        CDF::bottom()
    }

    fn sum_up(&self, other: &Self) -> Self {
        self.convolve(other)
    }

    fn add_prob(&self, other: &Self, do_offset: bool) -> Result<Self, Self::Error> {
        zip(self.iter(), other.iter(), 0.0, 0.0)
            .map(|(x, (y, z))| Ok((x, y.add_prob(&z, do_offset)?)))
            .collect()
    }

    fn scale_prob(&self, factor: f32) -> Self {
        self.iter().map(|(x, y)| (x, y * factor)).collect()
    }

    fn choice(&self, my_fraction: f32, other: &Self) -> Result<Self, Self::Error> {
        if my_fraction < 0.0 || my_fraction > 1.0 {
            return Err(CDFError::InvalidFraction(my_fraction));
        }
        let other_fraction = 1.0 - my_fraction;
        Ok(self
            .steps()
            .zip(other.steps())
            .map(|(x, (y, z))| (x, y * my_fraction + z * other_fraction))
            .collect())
    }

    fn compact(this: &mut Vec<(f32, Self)>, mode: CompactionMode, max_size: usize) {
        compact_cdf(this, mode, max_size);
    }

    fn similar(&self, other: &Self) -> bool {
        self.steps().similar(other.steps())
    }

    fn pretty_print(&self, f: &mut String) -> fmt::Result {
        let data = self.steps().data();
        if data.len() == 1 && data[0].1.similar(&1.0) {
            write!(f, "{:.5}", data[0].0)
        } else {
            write!(f, "{}", self)
        }
    }
}

pub trait StepValueMinMax: StepValue {
    fn min(&self, other: &Self) -> Self;
    fn max(&self, other: &Self) -> Self;
}

impl StepValueMinMax for f32 {
    fn min(&self, other: &Self) -> Self {
        f32::min(*self, *other)
    }

    fn max(&self, other: &Self) -> Self {
        f32::max(*self, *other)
    }
}
