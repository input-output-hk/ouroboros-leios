#[allow(unused_macros)]
macro_rules! cloned {
    ($($name:ident),*; $e:expr) => {{
        $(let $name = $name.clone();)*
        $e
    }};
}

mod agent;
mod cdf;
mod compaction;
mod delta_q;
mod outcome;
mod parser;
mod render;
mod step_function;

pub use agent::CalcCdf;
pub use cdf::{CDFError, CDF};
pub use compaction::{Compact, CompactionMode};
pub use delta_q::{DeltaQ, DeltaQExpr, EphemeralContext, PersistentContext};
pub use outcome::Outcome;
pub use render::{DeltaQComponent, DeltaQContext, EvalCtxAction};
pub use step_function::{StepFunction, StepFunctionError, DEFAULT_MAX_SIZE};
