#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, serde::Deserialize)]
pub struct Latency(f64);

impl Eq for Latency {}

impl Ord for Latency {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl std::ops::Add for Latency {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}

impl std::ops::AddAssign for Latency {
    fn add_assign(&mut self, other: Self) {
        self.0 += other.0;
    }
}

impl std::ops::Sub for Latency {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        if self.0 < other.0 {
            panic!("Latency cannot be negative");
        }
        Self(self.0 - other.0)
    }
}

impl std::ops::Mul<f64> for Latency {
    type Output = Self;

    fn mul(self, other: f64) -> Self {
        if other < 0.0 {
            panic!("Multiplication factor cannot be negative");
        }
        if other.is_nan() {
            panic!("Multiplication factor cannot be NaN");
        }
        Self(self.0 * other)
    }
}

impl std::ops::Div<f64> for Latency {
    type Output = Self;

    fn div(self, other: f64) -> Self {
        if other < 0.0 {
            panic!("Division factor cannot be negative");
        }
        if other.is_nan() {
            panic!("Division factor cannot be NaN");
        }
        Self(self.0 / other)
    }
}

impl std::ops::Div<Latency> for Latency {
    type Output = f64;

    fn div(self, other: Latency) -> Self::Output {
        self.0 / other.0
    }
}

impl TryFrom<f64> for Latency {
    type Error = String;

    fn try_from(value: f64) -> Result<Self, Self::Error> {
        Self::new(value).ok_or("Latency must be non-negative number".to_string())
    }
}

impl std::fmt::Display for Latency {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:.1}ms", self.0)
    }
}

impl Latency {
    pub fn new(latency: f64) -> Option<Self> {
        if latency.is_nan() || latency < 0.0 {
            None
        } else {
            Some(Self(latency))
        }
    }

    pub fn zero() -> Self {
        Self(0.0)
    }

    #[allow(dead_code)]
    pub fn infinity() -> Self {
        Self(f64::INFINITY)
    }

    pub fn as_f32(&self) -> f32 {
        self.0 as f32
    }

    #[allow(dead_code)]
    pub fn as_f64(&self) -> f64 {
        self.0
    }
}
