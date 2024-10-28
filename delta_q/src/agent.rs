use crate::{Outcome, PersistentContext};
use yew_agent::prelude::oneshot;

#[oneshot]
pub async fn CalcCdf((name, ctx): (String, PersistentContext)) -> Result<Outcome, String> {
    ctx.eval(&name).map_err(|e| e.to_string())
}
