use crate::{DeltaQ, EvaluationContext, CDF};
use yew_agent::prelude::oneshot;

#[oneshot]
pub async fn CalcCdf((name, mut ctx): (String, EvaluationContext)) -> Result<CDF, String> {
    DeltaQ::name(&name)
        .eval(&mut ctx)
        .map_err(|e| e.to_string())
}
