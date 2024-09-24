use std::cmp::Ordering;

#[derive(Debug, PartialEq)]
pub enum CDFError {
    InvalidDataRange,
    NonMonotonicData,
    BinSizeMismatch,
    LengthMismatch,
    InvalidFraction,
}

impl std::fmt::Display for CDFError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
        }
    }
}

impl std::error::Error for CDFError {}

/// A Cumulative Distribution Function (CDF) is a representation of a probability
/// distribution that can be manipulated in various ways.
#[derive(Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct CDF {
    data: Vec<u16>,
    bin_size: f32,
}

impl std::fmt::Debug for CDF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CDF")
            .field("data", &self.to_string())
            .field("bin_size", &self.bin_size)
            .field("len", &self.data.len())
            .finish()
    }
}

impl std::fmt::Display for CDF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut last_value = 0;
        write!(f, "CDF[")?;
        for (i, &value) in self.data.iter().enumerate() {
            let value_f32 = (value as f32 / 65535.0).min(1.0);
            if value != last_value {
                if last_value != 0 {
                    write!(f, ", ")?;
                }
                let x = i as f32 * self.bin_size;
                write!(f, "({:.4}, {:.4})", x, value_f32)?;
                last_value = value;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}

pub struct CDFIterator<'a> {
    cdf: &'a CDF,
    index: usize,
    last_value: u16,
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
        while self.index < self.cdf.data.len() {
            let value = self.cdf.data[self.index];
            let value_f32 = (value as f32 / 65535.0).min(1.0);
            if value != self.last_value {
                let x = self.index as f32 * self.cdf.bin_size;
                self.last_value = value;
                self.index += 1;
                return Some((x, value_f32));
            }
            self.index += 1;
        }
        if !self.last {
            self.last = true;
            Some((
                self.cdf.width(),
                (self.last_value as f32 / 65535.0).min(1.0),
            ))
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
        let converted_data: Vec<u16> = data.iter().map(|&x| (x * 65535.0) as u16).collect();
        Ok(Self {
            data: converted_data,
            bin_size,
        })
    }

    pub fn iter(&self) -> CDFIterator {
        CDFIterator {
            cdf: self,
            index: 0,
            last_value: 0,
            first: true,
            last: false,
        }
    }

    /// Get the width of the CDF.
    pub fn width(&self) -> f32 {
        self.data.len() as f32 * self.bin_size
    }

    /// Create a step function CDF from a vector of (x, y) pairs.
    /// The x values must be greater than 0 and must be strictly monotonically increasing.
    /// The y values must be from (0, 1] and must be strictly monotonically increasing.
    pub fn step(points: &[(f32, f32)], bin_size: f32, bins: usize) -> Result<Self, CDFError> {
        if !points.iter().all(|&(x, y)| x >= 0.0 && y > 0.0 && y <= 1.0) {
            return Err(CDFError::InvalidDataRange);
        }
        if !points
            .windows(2)
            .all(|w| w[0].0 < w[1].0 && w[0].1 < w[1].1)
        {
            return Err(CDFError::NonMonotonicData);
        }
        let mut data = vec![0u16; bins];
        for &(x, y) in points {
            let index = (x / bin_size).floor() as usize;
            data[index] = to_int(y);
        }
        for i in 1..data.len() {
            if data[i] == 0 {
                data[i] = data[i - 1];
            }
        }
        Ok(Self { data, bin_size })
    }

    /// Combine two CDFs by choosing between them, using the given fraction as the probability for
    /// the first CDF.
    pub fn choice(&self, fraction: f32, other: &CDF) -> Result<CDF, CDFError> {
        if self.bin_size != other.bin_size {
            return Err(CDFError::BinSizeMismatch);
        }
        if self.data.len() != other.data.len() {
            return Err(CDFError::LengthMismatch);
        }
        if fraction < 0.0 || fraction > 1.0 {
            return Err(CDFError::InvalidFraction);
        }
        let my_fraction = to_int(fraction);
        let fraction = 65535 - my_fraction;
        let combined_data: Vec<u16> = self
            .data
            .iter()
            .zip(&other.data)
            .map(|(&x, &y)| {
                mul(x, my_fraction)
                    .checked_add(mul(y, fraction))
                    .expect("addition overflow")
            })
            .collect();
        Ok(CDF {
            data: combined_data,
            bin_size: self.bin_size,
        })
    }

    /// Combine two CDFs by universal quantification, meaning that both outcomes must occur.
    pub fn for_all(&self, other: &CDF) -> Result<CDF, CDFError> {
        if self.bin_size != other.bin_size {
            return Err(CDFError::BinSizeMismatch);
        }
        if self.data.len() != other.data.len() {
            return Err(CDFError::LengthMismatch);
        }
        let multiplied_data: Vec<u16> = self
            .data
            .iter()
            .zip(&other.data)
            .map(|(&x, &y)| mul(x, y))
            .collect();
        Ok(CDF {
            data: multiplied_data,
            bin_size: self.bin_size,
        })
    }

    /// Combine two CDFs by existential quantification, meaning that at least one of the outcomes
    pub fn for_some(&self, other: &CDF) -> Result<CDF, CDFError> {
        if self.bin_size != other.bin_size {
            return Err(CDFError::BinSizeMismatch);
        }
        if self.data.len() != other.data.len() {
            return Err(CDFError::LengthMismatch);
        }
        let multiplied_data: Vec<u16> = self
            .data
            .iter()
            .zip(&other.data)
            .map(|(&x, &y)| {
                u16::try_from(
                    (x as u32 + y as u32)
                        .checked_sub(mul(x, y) as u32)
                        .expect("subtraction underflow during for_some"),
                )
                .expect("overflow during for_some")
            })
            .collect();
        Ok(CDF {
            data: multiplied_data,
            bin_size: self.bin_size,
        })
    }

    /// Convolve two CDFs, which is equivalent to taking the sum of all possible outcomes of the
    /// two CDFs. This describes the distribution of the sum of two independent random variables.
    pub fn convolve(&self, other: &CDF) -> Result<CDF, CDFError> {
        if self.bin_size != other.bin_size {
            return Err(CDFError::BinSizeMismatch);
        }
        if self.data.len() != other.data.len() {
            return Err(CDFError::LengthMismatch);
        }
        let len = self.data.len();
        let mut convolved_data: Vec<u16> = vec![0; len];
        for i in 0..len {
            for j in 0..len - i {
                let other = if j == 0 {
                    other.data[j]
                } else {
                    other.data[j] - other.data[j - 1]
                };
                convolved_data[i + j] += mul(self.data[i], other);
            }
        }
        Ok(CDF {
            data: convolved_data,
            bin_size: self.bin_size,
        })
    }
}

impl PartialOrd for CDF {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.bin_size != other.bin_size {
            return None;
        }
        let mut ret = None;
        for (l, r) in self.data.iter().zip(&other.data) {
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

fn mul(x: u16, y: u16) -> u16 {
    ((x as u32 * y as u32 + 65535) >> 16) as u16
}

fn to_int(x: f32) -> u16 {
    (x * 65536.0 + 0.5).min(65535.0) as u16
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let cdf = CDF::new(&[0.0, 0.25, 0.5, 0.75, 1.0], 0.25).unwrap();
        assert_eq!(cdf.data, vec![0, 16383, 32767, 49151, 65535]);
        assert_eq!(cdf.bin_size, 0.25);

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
        assert_eq!(result, CDF::new(&[0.0, 0.12501, 0.375, 1.0], 0.25).unwrap());
    }

    #[test]
    fn test_for_some() {
        let left = CDF::new(&[0.0, 0.5, 0.75, 1.0], 0.25).unwrap();
        let right = CDF::new(&[0.0, 0.25, 0.5, 1.0], 0.25).unwrap();
        let result = left.for_some(&right).unwrap();
        assert_eq!(result, CDF::new(&[0.0, 0.62499, 0.875, 1.0], 0.25).unwrap());
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
