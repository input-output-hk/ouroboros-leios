use iter_tools::Itertools;
use std::{
    cmp::Ordering,
    collections::BinaryHeap,
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

pub const DEFAULT_MAX_SIZE: usize = 1000;

/// A Cumulative Distribution Function (CDF) is a representation of a probability
/// distribution that can be manipulated in various ways.
#[derive(Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct CDF {
    /// invariants: first component strictly monotonically increasing and non-negative,
    /// second component strictly monotonically increasing and in the range (0, 1]
    data: Vec<(f32, f32)>,
    #[serde(skip)]
    max_size: usize,
    #[serde(skip)]
    mode: CompactionMode,
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

impl FromStr for CDF {
    type Err = CDFError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn err(s: &'static str, x: &str, y: &str) -> CDFError {
            CDFError::InvalidFormat(s, x.as_ptr() as usize - y.as_ptr() as usize)
        }

        let mut data = Vec::new();
        let mut x_prev = -1.0;
        let mut y_prev = 0.0;
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
            if x < 0.0 {
                return Err(CDFError::InvalidDataRange);
            }
            if x <= x_prev {
                return Err(CDFError::NonMonotonicData);
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
            if y <= 0.0 || y > 1.0 {
                return Err(CDFError::InvalidDataRange);
            }
            if y <= y_prev {
                return Err(CDFError::NonMonotonicData);
            }
            y_prev = y;
            data.push((x, y));
        }
        Ok(Self {
            data,
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
        })
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
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
        })
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

    pub fn iter(&self) -> CDFIterator {
        CDFIterator {
            cdf: self.data.iter(),
            prev: (0.0, 0.0),
            first: true,
            last: true,
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
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
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
        PairIterators::new(self.data.iter().copied(), other.data.iter().copied())
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
        compact(&mut data, self.mode, self.max_size);
        Ok(CDF { data, ..*self })
    }

    /// Combine two CDFs by universal quantification, meaning that both outcomes must occur.
    pub fn for_all(&self, other: &CDF) -> Result<CDF, CDFError> {
        let mut data = Vec::new();
        for (x, (ly, ry)) in self.zip_data(other) {
            let y = ly * ry;
            data.push((x, y));
        }
        compact(&mut data, self.mode, self.max_size);
        Ok(CDF { data, ..*self })
    }

    /// Combine two CDFs by existential quantification, meaning that at least one of the outcomes
    pub fn for_some(&self, other: &CDF) -> Result<CDF, CDFError> {
        let mut data = Vec::new();
        for (x, (ly, ry)) in self.zip_data(other) {
            let y = (ly + ry - ly * ry).clamp(0.0, 1.0);
            data.push((x, y));
        }
        compact(&mut data, self.mode, self.max_size);
        Ok(CDF { data, ..*self })
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
            let iter = PairIterators::new(
                data.iter().copied(),
                other.data.iter().map(|(x, y)| (x + lx, y * step)),
            );
            for (x, (ly, ry)) in iter {
                d.push((x, (ly + ry).min(1.0)));
            }
            data = d;
            prev_y = ly;
        }
        compact(&mut data, self.mode, self.max_size);
        Ok(CDF { data, ..*self })
    }
}

#[derive(Debug, PartialEq, Default, Clone, Copy)]
pub enum CompactionMode {
    #[default]
    UnderApproximate,
    OverApproximate,
}

/// Repeated computation with a CDF can lead to an unbounded number of data points, hence we limit its size.
/// This function ensures a maximal data length of `max_size` points by collapsing point pairs that are closest to each other on the x axis.
/// Under CompactionMode::UnderApproximate, the new point gets the greater x coordinate while under CompactionMode::OverApproximate, the new point gets the smaller x coordinate.
/// The resulting point always has the higher y value of the pair.
fn compact(data: &mut Vec<(f32, f32)>, mode: CompactionMode, max_size: usize) {
    if data.len() <= max_size {
        return;
    }
    // determine overall scale of the graph to determine the granularity of distances
    // (without this rounding the pruning will be dominated by floating point errors)
    let scale = data[data.len() - 1].0;
    let granularity = scale / 300.0;

    #[derive(Debug, PartialEq)]
    struct D(i16, usize, f32);
    impl Eq for D {}
    impl PartialOrd for D {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for D {
        fn cmp(&self, other: &Self) -> Ordering {
            other.0.cmp(&self.0).then_with(|| self.1.cmp(&other.1))
        }
    }
    let mk_d = |dist: f32, idx: usize| D((dist / granularity) as i16, idx, dist);

    // use a binary heap to pull the closest pairs, identifying them by their x coordinate and sorting them by the distance to their right neighbor.
    let mut heap = data
        .iter()
        .tuple_windows::<(&(f32, f32), &(f32, f32))>()
        .enumerate()
        .map(|(idx, (a, b))| {
            let dist = b.0 - a.0;
            mk_d(dist, idx)
        })
        .collect::<BinaryHeap<_>>();

    let mut to_remove = data.len() - max_size;
    let mut last_bin = -1;
    while let Some(D(bin, idx, dist)) = heap.pop() {
        if bin == last_bin {
            last_bin = -1;
            continue;
        } else {
            last_bin = bin;
        }
        if data[idx].1 == 0.0 {
            continue;
        }

        match mode {
            CompactionMode::UnderApproximate => {
                // just remove this point, meaning that the left neighbour needs to be updated
                if let Some(neighbour) = data[..idx].iter().rposition(|x| x.1 > 0.0) {
                    heap.push(mk_d(data[idx].0 - data[neighbour].0 + dist, idx));
                    data[idx] = data[neighbour];
                    data[neighbour].1 = 0.0;
                } else {
                    data[idx].1 = 0.0;
                }
            }
            CompactionMode::OverApproximate => {
                // we update the y on this point and remove the right neighbour
                let mut neighbours = data[idx + 1..]
                    .iter()
                    .enumerate()
                    .filter_map(|(i, (_x, y))| (*y > 0.0).then_some(idx + 1 + i));
                let n1 = neighbours.next();
                let n2 = neighbours.next();
                match (n1, n2) {
                    (Some(n1), Some(n2)) => {
                        // drop n1 and update our distance
                        heap.push(mk_d(data[n2].0 - data[idx].0, idx));
                        data[idx].1 = data[n1].1;
                        data[n1].1 = 0.0;
                    }
                    (Some(n1), None) => {
                        // n1 is the rightmost, so don't submit us again because now we’re rightmost
                        data[idx].1 = data[n1].1;
                        data[n1].1 = 0.0;
                    }
                    _ => {
                        debug_assert!(false, "shouldn’t get here because of the above");
                    }
                }
            }
        };

        to_remove -= 1;
        if to_remove == 0 {
            break;
        }
    }
    data.retain(|x| x.1 > 0.0);
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

/// Iterator over a pair of iterators, yielding the x value and the pair of y values for each
/// point where one of the iterators has a point.
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

impl<'a, L, R> PairIterators<'a, L, R>
where
    L: Iterator<Item = (f32, f32)> + 'a,
    R: Iterator<Item = (f32, f32)> + 'a,
{
    fn new(left: L, right: R) -> Self {
        Self {
            left: left.peekable(),
            l_prev: 0.0,
            right: right.peekable(),
            r_prev: 0.0,
            _ph: PhantomData,
        }
    }
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
        compact(&mut data1, CompactionMode::UnderApproximate, 5);
        assert_eq!(
            data1,
            vec![(0.1, 0.2), (0.3, 0.4), (0.5, 0.6), (0.7, 0.8), (0.9, 1.0)]
        );
        let mut data2 = data.clone();
        compact(&mut data2, CompactionMode::OverApproximate, 5);
        assert_eq!(
            data2,
            vec![(0.0, 0.2), (0.2, 0.4), (0.4, 0.6), (0.6, 0.8), (0.8, 1.0)]
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
        compact(&mut data1, CompactionMode::UnderApproximate, 5);
        assert_eq!(
            data1,
            vec![(0.1, 0.2), (0.3, 0.4), (0.5, 0.5), (0.7, 0.6), (0.9, 0.7)]
        );
        let mut data2 = data.clone();
        compact(&mut data2, CompactionMode::OverApproximate, 5);
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
        compact(&mut data1, CompactionMode::UnderApproximate, 5);
        assert_eq!(
            data1,
            vec![(0.0, 0.1), (0.2, 0.3), (0.5, 0.6), (0.7, 0.8), (0.9, 1.0)]
        );
        let mut data1 = data.clone();
        compact(&mut data1, CompactionMode::OverApproximate, 5);
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
        compact(&mut data1, CompactionMode::UnderApproximate, 5);
        assert_eq!(
            data1,
            vec![(0.1, 0.2), (0.3, 0.4), (0.5, 0.6), (0.7, 0.8), (0.9, 1.0)]
        );
        let mut data1 = data.clone();
        compact(&mut data1, CompactionMode::OverApproximate, 5);
        assert_eq!(
            data1,
            vec![(0.1, 0.2), (0.2, 0.4), (0.5, 0.6), (0.7, 0.8), (0.8, 1.0)]
        );
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
