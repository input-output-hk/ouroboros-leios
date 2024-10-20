#[allow(unused_macros)]
macro_rules! cloned {
    ($($name:ident),*; $e:expr) => {{
        $(let $name = $name.clone();)*
        $e
    }};
}

mod agent;
mod cdf;
mod delta_q;
mod parser;
mod render;
mod step_function;

pub use agent::CalcCdf;
pub use cdf::{CDFError, CDF};
pub use delta_q::{DeltaQ, EvaluationContext};
pub use render::{DeltaQComponent, DeltaQContext, EvalCtxAction};
pub use step_function::{CompactionMode, StepFunction, StepFunctionError, DEFAULT_MAX_SIZE};
