use crate::{DeltaQ, EvaluationContext, Outcome};
use yew_agent::prelude::oneshot;

#[oneshot]
pub async fn CalcCdf((name, mut ctx): (String, EvaluationContext)) -> Result<Outcome, String> {
    DeltaQ::name(&name)
        .eval(&mut ctx)
        .map_err(|e| e.to_string())
}
