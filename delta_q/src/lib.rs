#[allow(unused_macros)]
macro_rules! cloned {
    ($($name:ident),*; $e:expr) => {{
        $(let $name = $name.clone();)*
        $e
    }};
}

mod cdf;
mod delta_q;
#[cfg(feature = "web")]
mod render;

pub use cdf::{CDFError, CDF};
pub use delta_q::{DeltaQ, EvaluationContext};
#[cfg(feature = "web")]
pub use render::{cdf_to_svg, DeltaQComponent, DeltaQContext};
