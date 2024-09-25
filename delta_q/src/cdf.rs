use iter_tools::Itertools;
use std::{
    cmp::Ordering,
    fmt::{self, Write},
    iter::Peekable,
    marker::PhantomData,
    str::FromStr,
};

#[derive(Debug, PartialEq)]
pub enum CDFError {
    InvalidDataRange,
    NonMonotonicData,
    BinSizeMismatch,
    LengthMismatch,
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
            CDFError::BinSizeMismatch => write!(f, "CDFs must have the same bin size"),
            CDFError::LengthMismatch => write!(f, "CDFs must have the same length"),
            CDFError::InvalidFraction => write!(f, "Fraction must be between 0 and 1"),
            CDFError::InvalidFormat(s, pos) => write!(f, "Invalid format: {s} at {pos}"),
        }
    }
}

impl std::error::Error for CDFError {}

/// A Cumulative Distribution Function (CDF) is a representation of a probability
/// distribution that can be manipulated in various ways.
#[derive(Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct CDF {
    /// invariants: first component strictly monotonically increasing and non-negative,
    /// second component strictly monotonically increasing and in the range (0, 1]
    data: Vec<(f32, f32)>,
}

impl fmt::Debug for CDF {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CDF").field("data", &self.data).finish()
    }
}

impl fmt::Display for CDF {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut scratch = String::new();

        write!(f, "CDF[")?;
        for (i, (x, y)) in self.data.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(&mut scratch, "{:.5}, ", x)?;
            write!(f, "({}, ", trim(&scratch))?;
            scratch.clear();
            write!(&mut scratch, "{:.5}, ", y)?;
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

impl FromStr for CDF {
    type Err = CDFError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn err(s: &'static str, x: &str, y: &str) -> CDFError {
            CDFError::InvalidFormat(s, x.as_ptr() as usize - y.as_ptr() as usize)
        }

        let mut data = Vec::new();
        for (x, y) in s
            .trim()
            .trim_start_matches("CDF[")
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
            let y = y.trim();
            if y.chars().next_back() != Some(')') {
                let pos = y.char_indices().next_back().map(|(i, _)| i).unwrap_or(0);
                return Err(err("expecting ')'", &y[pos..], s));
            }
            let y: f32 = y[..y.len() - 1]
                .trim()
                .parse()
                .map_err(|_| err("expecting number", y, s))?;
            data.push((x, y));
        }
        Ok(Self { data })
    }
}

pub struct CDFIterator<'a> {
    cdf: std::slice::Iter<'a, (f32, f32)>,
    prev: (f32, f32),
    first: bool,
    last: bool,
}

impl<'a> Iterator for CDFIterator<'a> {
    type Item = (f32, f32);

    fn next(&mut self) -> Option<Self::Item> {
        if self.first {
            self.first = false;
            return Some((0.0, 0.0));
        }
        if let Some(pair) = self.cdf.next() {
            self.prev = *pair;
            Some(*pair)
        } else if self.last {
            self.last = false;
            let (x, y) = self.prev;
            Some((x * 1.2, y))
        } else {
            None
        }
    }
}

impl CDF {
    /// Create a new CDF from a vector of data and a bin size.
    /// The data vector must contain values between 0 and 1, and must be
    /// monotonically increasing.
    pub fn new(data: &[f32], bin_size: f32) -> Result<Self, CDFError> {
        if !data.iter().all(|&x| x >= 0.0 && x <= 1.0) {
            return Err(CDFError::InvalidDataRange);
        }
        if !data.windows(2).all(|w| w[0] <= w[1]) {
            return Err(CDFError::NonMonotonicData);
        }
        let mut prev = 0.0;
        Ok(Self {
            data: data
                .iter()
                .enumerate()
                .map(|(i, &x)| (i as f32 * bin_size, x))
                .filter(|&(_, y)| {
                    let ret = y > prev;
                    prev = y;
                    ret
                })
                .collect(),
        })
    }

    pub fn iter(&self) -> CDFIterator {
        self.iter0(true)
    }

    fn iter0(&self, duplicate_last: bool) -> CDFIterator {
        CDFIterator {
            cdf: self.data.iter(),
            prev: (0.0, 0.0),
            first: true,
            last: duplicate_last,
        }
    }

    /// Get the width of the CDF.
    pub fn width(&self) -> f32 {
        self.data.iter().next_back().map_or(0.0, |(x, _)| *x)
    }

    /// Create a step function CDF from a vector of (x, y) pairs.
    /// The x values must be greater than 0 and must be strictly monotonically increasing.
    /// The y values must be from (0, 1] and must be strictly monotonically increasing.
    pub fn step(points: &[(f32, f32)]) -> Result<Self, CDFError> {
        if !points.iter().all(|&(x, y)| x >= 0.0 && y > 0.0 && y <= 1.0) {
            return Err(CDFError::InvalidDataRange);
        }
        if !points
            .windows(2)
            .all(|w| w[0].0 < w[1].0 && w[0].1 < w[1].1)
        {
            return Err(CDFError::NonMonotonicData);
        }
        Ok(Self {
            data: points.to_vec(),
        })
    }

    fn zip_data<'a>(
        &'a self,
        other: &'a CDF,
    ) -> PairIterators<
        'a,
        impl Iterator<Item = (f32, f32)> + 'a,
        impl Iterator<Item = (f32, f32)> + 'a,
    > {
        PairIterators {
            left: self.data.iter().copied().peekable(),
            l_prev: 0.0,
            right: other.data.iter().copied().peekable(),
            r_prev: 0.0,
            _ph: PhantomData,
        }
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
        for (x, (ly, ry)) in self.zip_data(other) {
            let y = (ly * my_fraction + ry * fraction).min(1.0);
            if y > prev_y {
                prev_y = y;
                data.push((x, y));
            }
        }
        Ok(CDF { data })
    }

    /// Combine two CDFs by universal quantification, meaning that both outcomes must occur.
    pub fn for_all(&self, other: &CDF) -> Result<CDF, CDFError> {
        let mut data = Vec::new();
        for (x, (ly, ry)) in self.zip_data(other) {
            let y = ly * ry;
            data.push((x, y));
        }
        Ok(CDF { data })
    }

    /// Combine two CDFs by existential quantification, meaning that at least one of the outcomes
    pub fn for_some(&self, other: &CDF) -> Result<CDF, CDFError> {
        let mut data = Vec::new();
        for (x, (ly, ry)) in self.zip_data(other) {
            let y = (ly + ry - ly * ry).clamp(0.0, 1.0);
            data.push((x, y));
        }
        Ok(CDF { data })
    }

    /// Convolve two CDFs, which is equivalent to taking the sum of all possible outcomes of the
    /// two CDFs. This describes the distribution of the sum of two independent random variables.
    pub fn convolve(&self, other: &CDF) -> Result<CDF, CDFError> {
        // start with the all-zero CDF
        let mut data = Vec::new();
        let mut prev_y = 0.0;
        for &(lx, ly) in self.data.iter() {
            let step = ly - prev_y;
            // take the other CDF, scale it by the step size, shift it by the current x value, and add it into the data
            let mut d = Vec::new();
            let iter = PairIterators {
                left: data.iter().copied().peekable(),
                l_prev: 0.0,
                right: other
                    .data
                    .iter()
                    .map(|(x, y)| (x + lx, y * step))
                    .peekable(),
                r_prev: 0.0,
                _ph: PhantomData,
            };
            for (x, (ly, ry)) in iter {
                d.push((x, (ly + ry).min(1.0)));
            }
            data = d;
            prev_y = ly;
        }
        Ok(CDF { data })
    }
}

impl PartialOrd for CDF {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut ret = None;
        for (_x, (l, r)) in self.zip_data(other) {
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

struct PairIterators<'a, L, R>
where
    L: Iterator<Item = (f32, f32)> + 'a,
    R: Iterator<Item = (f32, f32)> + 'a,
{
    left: Peekable<L>,
    l_prev: f32,
    right: Peekable<R>,
    r_prev: f32,
    _ph: PhantomData<&'a ()>,
}

impl<'a, L, R> Iterator for PairIterators<'a, L, R>
where
    L: Iterator<Item = (f32, f32)> + 'a,
    R: Iterator<Item = (f32, f32)> + 'a,
{
    /// yields (x, (left_y, right_y))
    type Item = (f32, (f32, f32));

    fn next(&mut self) -> Option<Self::Item> {
        match (self.left.peek(), self.right.peek()) {
            (Some(&(lx, ly)), Some(&(rx, ry))) => match lx.total_cmp(&rx) {
                Ordering::Less => {
                    self.l_prev = self.left.next().unwrap().1;
                    Some((lx, (ly, self.r_prev)))
                }
                Ordering::Greater => {
                    self.r_prev = self.right.next().unwrap().1;
                    Some((rx, (self.l_prev, ry)))
                }
                Ordering::Equal => {
                    self.l_prev = self.left.next().unwrap().1;
                    self.r_prev = self.right.next().unwrap().1;
                    Some((lx, (ly, ry)))
                }
            },
            (Some(&(lx, ly)), None) => {
                self.l_prev = self.left.next().unwrap().1;
                Some((lx, (ly, self.r_prev)))
            }
            (None, Some(&(rx, ry))) => {
                self.r_prev = self.right.next().unwrap().1;
                Some((rx, (self.l_prev, ry)))
            }
            (None, None) => None,
        }
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
}
