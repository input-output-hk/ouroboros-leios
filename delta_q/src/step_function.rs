use crate::{Compact, CompactionMode};
use itertools::Itertools;
use std::{
    cmp::Ordering,
    fmt::{self, Write},
    iter::Peekable,
    str::FromStr,
    sync::Arc,
};

#[derive(Debug)]
pub enum StepFunctionError {
    InvalidFormat(&'static str, usize),
    InvalidDataRange,
    NonMonotonicData,
}

impl fmt::Display for StepFunctionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidFormat(s, pos) => write!(f, "invalid format: {} at position {}", s, pos),
            Self::InvalidDataRange => write!(f, "invalid data range"),
            Self::NonMonotonicData => write!(f, "non-monotonic data"),
        }
    }
}
impl std::error::Error for StepFunctionError {}

pub const DEFAULT_MAX_SIZE: usize = 10000;

/// A step function represented as a list of (x, y) pairs.
#[derive(Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(try_from = "StepFunctionSerial<T>", into = "StepFunctionSerial<T>")]
pub struct StepFunction<T = f32>
where
    T: Clone + Default,
{
    /// invariants: first component strictly monotonically increasing and non-negative,
    /// with neighbouring x values being separated by at least five ε
    data: Option<Arc<[(f32, T)]>>,
    max_size: usize,
    mode: CompactionMode,
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
        if !points.iter().all(|&(x, y)| x >= 0.0 && y >= 0.0) {
            return Err(StepFunctionError::InvalidDataRange);
        }
        if !points.windows(2).all(|w| w[0].0 < w[1].0) {
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
        })
    }

    pub fn compact(&self, mut data: Vec<(f32, f32)>) -> Result<Self, StepFunctionError> {
        f32::compact(&mut data, self.mode, self.max_size);
        Self::new(&data)
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

impl<T> StepFunction<T>
where
    T: Clone + Default,
{
    pub fn zero() -> Self {
        Self {
            data: None,
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
        }
    }

    pub fn at(&self, x: f32) -> T {
        self.data().iter().rev().find(|&&(x0, _)| x0 <= x).map_or(
            self.data().last().map_or(T::default(), |(_x, y)| y.clone()),
            |(_, y)| y.clone(),
        )
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

    pub fn data(&self) -> &[(f32, T)] {
        self.data.as_deref().unwrap_or(&[])
    }

    pub fn iter(&self) -> StepFunctionIterator<T> {
        StepFunctionIterator {
            cdf: self.data().iter(),
            prev: (0.0, T::default()),
            first: false,
            last: false,
        }
    }

    pub fn graph_iter(&self) -> StepFunctionIterator<T> {
        StepFunctionIterator {
            cdf: self.data().iter(),
            prev: (0.0, T::default()),
            first: true,
            last: false,
        }
    }

    pub fn func_iter(&self) -> StepFunctionIterator<T> {
        StepFunctionIterator {
            cdf: self.data().iter(),
            prev: (0.0, T::default()),
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
    ) -> impl Iterator<Item = (f32, (T, T))> + 'a {
        PairIterators::new(self.data().iter().cloned(), other.data().iter().cloned())
    }

    pub fn mult(&self, factor: f32) -> Self
    where
        for<'a> &'a T: std::ops::Mul<f32, Output = T>,
    {
        if factor == 0.0 {
            return Self::zero()
                .with_max_size(self.max_size)
                .with_mode(self.mode);
        }
        Self {
            data: self
                .data
                .as_ref()
                .map(|d| d.iter().map(|(x, y)| (*x, y * factor)).collect()),
            max_size: self.max_size,
            mode: self.mode,
        }
    }

    pub fn add(&self, other: &Self) -> Self
    where
        T: std::ops::Add<T, Output = T> + Compact,
    {
        let mut data = Vec::new();
        for (x, (l, r)) in self.zip(other) {
            data.push((x, l + r));
        }
        T::compact(&mut data, self.mode, self.max_size);
        Self {
            data: (!data.is_empty()).then_some(data.into()),
            max_size: self.max_size,
            mode: self.mode,
        }
    }

    pub fn choice(&self, my_fraction: f32, other: &Self) -> Self
    where
        T: std::ops::Mul<f32, Output = T> + std::ops::Add<T, Output = T> + Compact,
    {
        let mut data = Vec::new();
        for (x, (l, r)) in self.zip(other) {
            data.push((x, l * my_fraction + r * (1.0 - my_fraction)));
        }
        T::compact(&mut data, self.mode, self.max_size);
        Self {
            data: (!data.is_empty()).then_some(data.into()),
            max_size: self.max_size,
            mode: self.mode,
        }
    }

    pub fn similar(&self, other: &Self) -> bool
    where
        T: Compact,
    {
        self.data().len() == other.data().len()
            && self
                .data()
                .iter()
                .zip(other.data().iter())
                .all(|(a, b)| f32::similar(&a.0, &b.0) && T::similar(&a.1, &b.1))
    }
}

impl<T> From<StepFunction<T>> for StepFunctionSerial<T>
where
    T: Clone + Default,
{
    fn from(cdf: StepFunction<T>) -> Self {
        Self {
            data: cdf.data()[..].to_owned(),
        }
    }
}

impl<T> TryFrom<StepFunctionSerial<T>> for StepFunction<T>
where
    T: Clone + Default,
{
    type Error = StepFunctionError;

    fn try_from(serial: StepFunctionSerial<T>) -> Result<Self, Self::Error> {
        let points = &serial.data;
        if !points.iter().all(|(x, _y)| *x >= 0.0) {
            return Err(StepFunctionError::InvalidDataRange);
        }
        if !points.windows(2).all(|w| w[0].0 < w[1].0) {
            return Err(StepFunctionError::NonMonotonicData);
        }
        let data = if points.is_empty() {
            None
        } else {
            Some(points.as_slice().into())
        };
        Ok(Self {
            data,
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
        })
    }
}

impl<T> fmt::Debug for StepFunction<T>
where
    T: Clone + Default + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StepFunction")
            .field("data", &self.data())
            .finish()
    }
}

impl<T> fmt::Display for StepFunction<T>
where
    T: Clone + Default + fmt::Display,
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
            write!(&mut scratch, "{:.5}", y)?;
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
                return Err(StepFunctionError::InvalidDataRange);
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
                return Err(StepFunctionError::InvalidDataRange);
            }
            data.push((x, y));
        }
        Ok(Self {
            data: (!data.is_empty()).then_some(data.into()),
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
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
    T: Clone + Default,
{
    type Item = (f32, T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.first {
            self.first = false;
            Some((0.0, T::default()))
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

impl<'a, T> std::iter::FusedIterator for StepFunctionIterator<'a, T> where T: Clone + Default {}

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

/// Iterator over a pair of iterators, yielding the x value and the pair of y values for each
/// point where one of the iterators has a point.
///
/// This iterator will coalesce points with approximately the same x value.
pub(crate) struct PairIterators<I1, I2, T>
where
    I1: Iterator<Item = (f32, T)>,
    I2: Iterator<Item = (f32, T)>,
    T: Clone,
{
    left: AggregatingIterator<I1, T>,
    l_prev: T,
    right: AggregatingIterator<I2, T>,
    r_prev: T,
}

impl<I1, I2, T> PairIterators<I1, I2, T>
where
    I1: Iterator<Item = (f32, T)>,
    I2: Iterator<Item = (f32, T)>,
    T: Clone + Default,
{
    pub fn new(left: I1, right: I2) -> Self {
        Self {
            left: AggregatingIterator::new(left),
            l_prev: T::default(),
            right: AggregatingIterator::new(right),
            r_prev: T::default(),
        }
    }
}

impl<I1, I2, T> Iterator for PairIterators<I1, I2, T>
where
    I1: Iterator<Item = (f32, T)>,
    I2: Iterator<Item = (f32, T)>,
    T: Clone,
{
    /// yields (x, (left_y, right_y))
    type Item = (f32, (T, T));

    fn next(&mut self) -> Option<Self::Item> {
        let left = self.left.peek();
        let right = self.right.peek();

        match (left, right) {
            (Some((lx, ly)), Some((rx, ry))) => {
                if (lx - rx).abs() / rx.max(1.0e-10) <= 5.0 * f32::EPSILON {
                    self.l_prev = self.left.next().unwrap().1;
                    self.r_prev = self.right.next().unwrap().1;
                    Some((lx, (ly, ry)))
                } else if lx < rx {
                    self.l_prev = self.left.next().unwrap().1;
                    Some((lx, (ly, self.r_prev.clone())))
                } else {
                    self.r_prev = self.right.next().unwrap().1;
                    Some((rx, (self.l_prev.clone(), ry)))
                }
            }
            (Some((lx, ly)), None) => {
                self.l_prev = self.left.next().unwrap().1;
                Some((lx, (ly, self.r_prev.clone())))
            }
            (None, Some((rx, ry))) => {
                self.r_prev = self.right.next().unwrap().1;
                Some((rx, (self.l_prev.clone(), ry)))
            }
            (None, None) => None,
        }
    }
}

/// An iterator that aggregates values for which the first component of the pair
/// is within 5*f32::EPSILON of each other.
pub struct AggregatingIterator<I: Iterator, T> {
    inner: Peekable<I>,
    current: Option<(f32, T)>,
}

impl<I, T> AggregatingIterator<I, T>
where
    I: Iterator<Item = (f32, T)>,
    T: Clone,
{
    pub fn new(iter: I) -> Self {
        AggregatingIterator {
            inner: iter.peekable(),
            current: None,
        }
    }

    fn peek(&mut self) -> Option<(f32, T)> {
        if self.current.is_some() {
            // already computed
            return self.current.clone();
        } else {
            // compute the next value
            self.current = self.inner.next();
        }

        let first = self.current.clone()?;
        let mut last = first.clone();

        while let Some(next) = self.inner.peek() {
            if (next.0 - first.0).abs() / first.0 <= 5.0 * f32::EPSILON {
                last = next.clone();
                self.inner.next();
            } else {
                break;
            }
        }

        self.current = Some((first.0 + (last.0 - first.0) / 2.0, last.1));
        self.current.clone()
    }
}

impl<I, T> Iterator for AggregatingIterator<I, T>
where
    I: Iterator<Item = (f32, T)>,
    T: Clone,
{
    type Item = (f32, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.peek();
        self.current.take()
    }
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
}
