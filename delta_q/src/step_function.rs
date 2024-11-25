use crate::{compaction::simplify_cdf, CompactionMode, StepValue, CDF};
use itertools::Itertools;
use std::{
    cmp::Ordering,
    fmt::{self, Write},
    str::FromStr,
    sync::Arc,
};

#[derive(Debug)]
pub enum StepFunctionError {
    InvalidFormat(&'static str, usize),
    InvalidDataRange(&'static str, f32),
    NonMonotonicData,
    InvalidFraction(f32),
    ProbabilityOverflow(f32),
}

impl fmt::Display for StepFunctionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidFormat(s, pos) => write!(f, "invalid format: {} at position {}", s, pos),
            Self::InvalidDataRange(axis, y) => write!(f, "invalid data range: {axis}={y}"),
            Self::NonMonotonicData => write!(f, "non-monotonic data"),
            Self::InvalidFraction(y) => {
                write!(f, "invalid fraction: {y} (must be between 0 and 1)")
            }
            Self::ProbabilityOverflow(y) => write!(f, "probability overflow: {y}"),
        }
    }
}
impl std::error::Error for StepFunctionError {}

pub const DEFAULT_MAX_SIZE: usize = 1000;

/// A step function represented as a list of (x, y) pairs.
#[derive(Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(try_from = "StepFunctionSerial<T>", into = "StepFunctionSerial<T>")]
pub struct StepFunction<T: StepValue = f32> {
    /// invariants: first component strictly monotonically increasing and non-negative,
    /// with neighbouring x values being separated by at least five ε
    data: Option<Arc<[(f32, T)]>>,
    max_size: usize,
    mode: CompactionMode,
    zero: T,
}

#[derive(serde::Serialize, serde::Deserialize)]
struct StepFunctionSerial<T> {
    data: Vec<(f32, T)>,
}

impl StepFunction {
    /// Create a step function CDF from a vector of (x, y) pairs.
    /// The x values must be greater than 0 and must be strictly monotonically increasing.
    /// The y values must be from (0, 1] and must be strictly monotonically increasing.
    pub fn new(points: &[(f32, f32)]) -> Result<Self, StepFunctionError> {
        for &(x, y) in points.iter() {
            if x < 0.0 {
                return Err(StepFunctionError::InvalidDataRange("x", x));
            }
            if y < 0.0 {
                return Err(StepFunctionError::InvalidDataRange("y", y));
            }
        }
        if !points.windows(2).all(|w| w[0].0 < w[1].0) {
            #[cfg(target_arch = "wasm32")]
            web_sys::console::error_2(&"non-monotonic".into(), &format!("{:?}", points).into());
            return Err(StepFunctionError::NonMonotonicData);
        }
        let data = if points.is_empty() {
            None
        } else {
            Some(points.into())
        };
        Ok(Self {
            data,
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
            zero: 0.0,
        })
    }

    pub fn integrate(&self, from: f32, to: f32) -> f32 {
        self.func_iter()
            .tuple_windows()
            .filter_map(|((x0, y), (x1, _y))| {
                let min = x0.max(from);
                let max = x1.min(to);
                if min < max {
                    Some((max - min) * y)
                } else {
                    None
                }
            })
            .sum()
    }
}

impl StepFunction<CDF> {
    pub fn simplify(&self) -> Self {
        let mut data = self.data().to_vec();
        simplify_cdf(&mut data);
        Self {
            data: (!data.is_empty()).then_some(data.into()),
            max_size: self.max_size,
            mode: self.mode,
            zero: CDF::sum_up_zero(),
        }
    }
}

impl<T: StepValue> StepFunction<T> {
    pub fn zero() -> Self {
        Self {
            data: None,
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
            zero: T::sum_up_zero(),
        }
    }

    pub fn at(&self, x: f32) -> T {
        self.data()
            .iter()
            .rev()
            .find(|&&(x0, _)| x0 <= x)
            .map_or(T::sum_up_zero(), |(_, y)| y.clone())
    }

    /// Set the maximum size of the CDF using a mutable reference.
    pub fn set_max_size(&mut self, max_size: usize) {
        self.max_size = max_size;
    }

    /// Set the compaction mode of the CDF using a mutable reference.
    pub fn set_mode(&mut self, mode: CompactionMode) {
        self.mode = mode;
    }

    /// Set the maximum size of the CDF using builder pattern.
    pub fn with_max_size(mut self, max_size: usize) -> Self {
        self.max_size = max_size;
        self
    }

    /// Set the compaction mode of the CDF using builder pattern.
    pub fn with_mode(mut self, mode: CompactionMode) -> Self {
        self.mode = mode;
        self
    }

    pub fn max_size(&self) -> usize {
        self.max_size
    }

    pub fn mode(&self) -> CompactionMode {
        self.mode
    }

    pub fn data(&self) -> &[(f32, T)] {
        self.data.as_deref().unwrap_or(&[])
    }

    pub fn iter(&self) -> StepFunctionIterator<T> {
        StepFunctionIterator {
            cdf: self.data().iter(),
            prev: (0.0, T::sum_up_zero()),
            first: false,
            last: false,
        }
    }

    pub fn graph_iter(&self) -> StepFunctionIterator<T> {
        StepFunctionIterator {
            cdf: self.data().iter(),
            prev: (0.0, T::sum_up_zero()),
            first: true,
            last: false,
        }
    }

    pub fn func_iter(&self) -> StepFunctionIterator<T> {
        StepFunctionIterator {
            cdf: self.data().iter(),
            prev: (0.0, T::sum_up_zero()),
            first: true,
            last: true,
        }
    }

    /// Get the width of the CDF.
    pub fn max_x(&self) -> f32 {
        self.data().iter().next_back().map_or(0.0, |(x, _)| *x)
    }

    pub fn zip<'a>(
        &'a self,
        other: &'a StepFunction<T>,
    ) -> impl Iterator<Item = (f32, (&'a T, &'a T))> + 'a {
        zip(
            self.data().iter().map(|(x, y)| (*x, y)),
            other.data().iter().map(|(x, y)| (*x, y)),
            &self.zero,
            &other.zero,
        )
    }

    pub fn map<U: StepValue>(&self, f: impl Fn(&T) -> U) -> StepFunction<U> {
        StepFunction::<U> {
            data: self
                .data
                .as_ref()
                .map(|d| d.iter().map(|(x, y)| (*x, f(y))).collect()),
            max_size: self.max_size,
            mode: self.mode,
            zero: U::sum_up_zero(),
        }
    }

    pub fn sum_up(&self, other: &Self) -> Self {
        let mut data = Vec::new();
        for (x, (l, r)) in self.zip(other) {
            data.push((x, l.sum_up(&r)));
        }
        T::compact(&mut data, self.mode, self.max_size);
        Self {
            data: (!data.is_empty()).then_some(data.into()),
            max_size: self.max_size,
            mode: self.mode,
            zero: T::sum_up_zero(),
        }
    }

    pub fn choice(&self, my_fraction: f32, other: &Self) -> Result<Self, T::Error> {
        let mut data = Vec::new();
        for (x, (l, r)) in self.zip(other) {
            data.push((x, l.choice(my_fraction, r)?));
        }
        T::compact(&mut data, self.mode, self.max_size);
        Ok(Self {
            data: (!data.is_empty()).then_some(data.into()),
            max_size: self.max_size,
            mode: self.mode,
            zero: T::sum_up_zero(),
        })
    }

    pub fn similar(&self, other: &Self) -> bool {
        self.data().len() == other.data().len()
            && self
                .data()
                .iter()
                .zip(other.data().iter())
                .all(|(a, b)| f32::similar(&a.0, &b.0) && T::similar(&a.1, &b.1))
    }
}

impl<T: StepValue> From<StepFunction<T>> for StepFunctionSerial<T> {
    fn from(cdf: StepFunction<T>) -> Self {
        Self {
            data: cdf.data()[..].to_owned(),
        }
    }
}

impl<T: StepValue, const N: usize> TryFrom<&[(f32, T); N]> for StepFunction<T> {
    type Error = StepFunctionError;

    fn try_from(points: &[(f32, T); N]) -> Result<Self, Self::Error> {
        points.as_slice().try_into()
    }
}

impl<T: StepValue> TryFrom<&[(f32, T)]> for StepFunction<T> {
    type Error = StepFunctionError;

    fn try_from(points: &[(f32, T)]) -> Result<Self, Self::Error> {
        for (x, _y) in points.iter() {
            if *x < 0.0 {
                return Err(StepFunctionError::InvalidDataRange("x", *x));
            }
        }
        if !points.windows(2).all(|w| w[0].0 < w[1].0) {
            #[cfg(target_arch = "wasm32")]
            web_sys::console::error_2(&"non-monotonic".into(), &format!("{:?}", points).into());
            return Err(StepFunctionError::NonMonotonicData);
        }
        let data = if points.is_empty() {
            None
        } else {
            Some(points.into())
        };
        Ok(Self {
            data,
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
            zero: T::sum_up_zero(),
        })
    }
}

impl<T: StepValue> TryFrom<Vec<(f32, T)>> for StepFunction<T> {
    type Error = StepFunctionError;

    fn try_from(points: Vec<(f32, T)>) -> Result<Self, Self::Error> {
        points.as_slice().try_into()
    }
}

impl<T: StepValue> TryFrom<StepFunctionSerial<T>> for StepFunction<T> {
    type Error = StepFunctionError;

    fn try_from(serial: StepFunctionSerial<T>) -> Result<Self, Self::Error> {
        serial.data.as_slice().try_into()
    }
}

impl<T> fmt::Debug for StepFunction<T>
where
    T: StepValue + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StepFunction")
            .field("data", &self.data())
            .finish()
    }
}

impl<T> fmt::Display for StepFunction<T>
where
    T: StepValue,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut scratch = String::new();

        write!(f, "[")?;
        for (i, (x, y)) in self.data().iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(&mut scratch, "{:.5}", x)?;
            write!(f, "({}, ", trim(&scratch))?;
            scratch.clear();
            y.pretty_print(&mut scratch)?;
            write!(f, "{})", trim(&scratch))?;
            scratch.clear();
        }
        write!(f, "]")?;
        Ok(())
    }
}

fn trim(s: &str) -> &str {
    s.trim_end_matches('0').trim_end_matches('.')
}

impl FromStr for StepFunction {
    type Err = StepFunctionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn err(s: &'static str, x: &str, y: &str) -> StepFunctionError {
            StepFunctionError::InvalidFormat(s, x.as_ptr() as usize - y.as_ptr() as usize)
        }

        let mut data = Vec::new();
        let mut x_prev = -1.0;
        for (x, y) in s
            .trim()
            .trim_start_matches("[")
            .trim_end_matches("]")
            .split(',')
            .tuples()
        {
            let x = x.trim();
            if x.chars().next() != Some('(') {
                return Err(err("expecting '('", x, s));
            }
            let x: f32 = x[1..]
                .trim()
                .parse()
                .map_err(|_| err("expecting number", &x[1..], s))?;
            if x < 0.0 {
                return Err(StepFunctionError::InvalidDataRange("x", x));
            }
            if x <= x_prev {
                return Err(StepFunctionError::NonMonotonicData);
            }
            x_prev = x;
            let y = y.trim();
            if y.chars().next_back() != Some(')') {
                let pos = y.char_indices().next_back().map(|(i, _)| i).unwrap_or(0);
                return Err(err("expecting ')'", &y[pos..], s));
            }
            let y: f32 = y[..y.len() - 1]
                .trim()
                .parse()
                .map_err(|_| err("expecting number", y, s))?;
            if y < 0.0 {
                return Err(StepFunctionError::InvalidDataRange("y", y));
            }
            data.push((x, y));
        }
        Ok(Self {
            data: (!data.is_empty()).then_some(data.into()),
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
            zero: 0.0,
        })
    }
}

pub struct StepFunctionIterator<'a, T> {
    cdf: std::slice::Iter<'a, (f32, T)>,
    prev: (f32, T),
    first: bool,
    last: bool,
}

impl<'a, T> Iterator for StepFunctionIterator<'a, T>
where
    T: Clone + StepValue,
{
    type Item = (f32, T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.first {
            self.first = false;
            Some((0.0, T::sum_up_zero()))
        } else if let Some(pair) = self.cdf.next() {
            self.prev = pair.clone();
            Some(pair.clone())
        } else if self.last {
            self.last = false;
            Some((f32::INFINITY, self.prev.1.clone()))
        } else {
            None
        }
    }
}

impl<'a, T> std::iter::FusedIterator for StepFunctionIterator<'a, T> where T: Clone + StepValue {}

impl PartialOrd for StepFunction {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut ret = None;
        for (_x, (l, r)) in self.zip(other) {
            if l < r {
                if ret == Some(Ordering::Greater) {
                    return None;
                }
                ret = Some(Ordering::Less);
            } else if l > r {
                if ret == Some(Ordering::Less) {
                    return None;
                }
                ret = Some(Ordering::Greater);
            }
        }
        ret.or(Some(Ordering::Equal))
    }
}

/// Iterator over a pair of iterators that emit pairs ordered by their first component,
/// coalescing points with approximately the same x value.
pub fn zip<T1: Clone, T2: Clone>(
    left: impl Iterator<Item = (f32, T1)>,
    right: impl Iterator<Item = (f32, T2)>,
    mut l_prev: T1,
    mut r_prev: T2,
) -> impl Iterator<Item = (f32, (T1, T2))> {
    fn similar_cmp(a: f32, b: f32) -> Ordering {
        if f32::similar(&a, &b) {
            Ordering::Equal
        } else if a < b {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    }

    let left = left.coalesce(|a, b| {
        if f32::similar(&a.0, &b.0) {
            Ok((a.0 + (b.0 - a.0) / 2.0, b.1))
        } else {
            Err((a, b))
        }
    });
    let right = right.coalesce(|a, b| {
        if f32::similar(&a.0, &b.0) {
            Ok((a.0 + (b.0 - a.0) / 2.0, b.1))
        } else {
            Err((a, b))
        }
    });

    left.merge_join_by(right, |a, b| similar_cmp(a.0, b.0))
        .map(move |eob| match eob {
            itertools::EitherOrBoth::Both(l, r) => {
                l_prev = l.1.clone();
                r_prev = r.1.clone();
                (l.0, (l.1, r.1))
            }
            itertools::EitherOrBoth::Left(l) => {
                l_prev = l.1.clone();
                (l.0, (l.1, r_prev.clone()))
            }
            itertools::EitherOrBoth::Right(r) => {
                r_prev = r.1.clone();
                (r.0, (l_prev.clone(), r.1))
            }
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compact_even() {
        let data = vec![
            (0.0, 0.1),
            (0.1, 0.2),
            (0.2, 0.3),
            (0.3, 0.4),
            (0.4, 0.5),
            (0.5, 0.6),
            (0.6, 0.7),
            (0.7, 0.8),
            (0.8, 0.9),
            (0.9, 1.0),
        ];
        let mut data1 = data.clone();
        f32::compact(&mut data1, CompactionMode::UnderApproximate, 5);
        assert_eq!(
            data1,
            vec![(0.0, 0.1), (0.1, 0.2), (0.3, 0.4), (0.5, 0.6), (0.9, 1.0)]
        );
        let mut data2 = data.clone();
        f32::compact(&mut data2, CompactionMode::OverApproximate, 5);
        assert_eq!(
            data2,
            vec![(0.0, 0.3), (0.3, 0.5), (0.5, 0.7), (0.7, 0.9), (0.9, 1.0)]
        );
    }

    #[test]
    fn test_compact_begin() {
        let data = vec![
            (0.0, 0.1),
            (0.1, 0.2),
            (0.2, 0.3),
            (0.3, 0.4),
            (0.5, 0.5),
            (0.7, 0.6),
            (0.9, 0.7),
        ];
        let mut data1 = data.clone();
        f32::compact(&mut data1, CompactionMode::UnderApproximate, 5);
        assert_eq!(
            data1,
            vec![(0.0, 0.1), (0.1, 0.2), (0.3, 0.4), (0.5, 0.5), (0.9, 0.7)]
        );
        let mut data2 = data.clone();
        f32::compact(&mut data2, CompactionMode::OverApproximate, 5);
        assert_eq!(
            data2,
            vec![(0.0, 0.2), (0.2, 0.4), (0.5, 0.5), (0.7, 0.6), (0.9, 0.7)]
        );
    }

    #[test]
    fn test_compact_middle() {
        let data = vec![
            (0.0, 0.1),
            (0.2, 0.3),
            (0.4, 0.5),
            (0.5, 0.6),
            (0.7, 0.8),
            (0.9, 1.0),
        ];
        let mut data1 = data.clone();
        f32::compact(&mut data1, CompactionMode::UnderApproximate, 5);
        assert_eq!(
            data1,
            vec![(0.0, 0.1), (0.2, 0.3), (0.5, 0.6), (0.7, 0.8), (0.9, 1.0)]
        );
        let mut data1 = data.clone();
        f32::compact(&mut data1, CompactionMode::OverApproximate, 5);
        assert_eq!(
            data1,
            vec![(0.0, 0.1), (0.2, 0.3), (0.4, 0.6), (0.7, 0.8), (0.9, 1.0)]
        );
    }

    #[test]
    fn test_compact_edges() {
        let data = vec![
            (0.1, 0.2),
            (0.2, 0.3),
            (0.3, 0.4),
            (0.5, 0.6),
            (0.7, 0.8),
            (0.8, 0.9),
            (0.9, 1.0),
        ];
        let mut data1 = data.clone();
        f32::compact(&mut data1, CompactionMode::UnderApproximate, 5);
        assert_eq!(
            data1,
            vec![(0.1, 0.2), (0.3, 0.4), (0.5, 0.6), (0.7, 0.8), (0.9, 1.0)]
        );
        let mut data1 = data.clone();
        f32::compact(&mut data1, CompactionMode::OverApproximate, 5);
        assert_eq!(
            data1,
            vec![(0.1, 0.3), (0.3, 0.4), (0.5, 0.6), (0.7, 0.9), (0.9, 1.0)]
        );
    }

    #[test]
    fn test_at() {
        let sf = StepFunction::from_str("[(0.5, 0.1), (1, 1)]").unwrap();
        assert_eq!(sf.at(-1.0), 0.0);
        assert_eq!(sf.at(0.0), 0.0);
        assert_eq!(sf.at(0.5), 0.1);
        assert_eq!(sf.at(1.0), 1.0);
        assert_eq!(sf.at(1.5), 1.0);
    }
}
