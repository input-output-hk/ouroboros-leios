use crate::{delta_q::Name, CDFError, EvaluationContext, StepFunction, CDF};
use itertools::{EitherOrBoth, Itertools};
use std::{
    collections::BTreeMap,
    fmt::{self, Display},
};

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Outcome {
    pub cdf: CDF,
    pub load: BTreeMap<Name, StepFunction>,
}

impl Outcome {
    pub fn new(cdf: CDF) -> Self {
        Self {
            cdf,
            load: BTreeMap::new(),
        }
    }

    pub fn new_with_load(cdf: CDF, load: BTreeMap<Name, StepFunction>) -> Self {
        Self { cdf, load }
    }

    pub fn cdf(&self) -> &CDF {
        &self.cdf
    }

    pub fn load(&self) -> &BTreeMap<Name, StepFunction> {
        &self.load
    }

    pub fn with_load(mut self, metric: Name, load: StepFunction) -> Self {
        self.load.insert(metric, load);
        self
    }

    fn cdf_cloned(&self, ctx: &EvaluationContext) -> CDF {
        self.cdf
            .clone()
            .with_max_size(ctx.max_size)
            .with_mode(ctx.mode)
    }

    fn map_load(
        &self,
        ctx: &EvaluationContext,
        f: impl Fn(&StepFunction) -> StepFunction,
    ) -> BTreeMap<Name, StepFunction> {
        self.load.iter().map(|(n, l)| (n.clone(), f(l))).collect()
    }

    fn map_loads(
        &self,
        other: &Self,
        ctx: &EvaluationContext,
        f: impl Fn(&StepFunction, &StepFunction) -> Result<StepFunction, CDFError>,
    ) -> Result<BTreeMap<Name, StepFunction>, CDFError> {
        self.load
            .iter()
            .merge_join_by(other.load.iter(), |(nl, _), (nr, _)| nl.cmp(nr))
            .map(|x| match x {
                EitherOrBoth::Left((n, l)) => Ok((n.clone(), f(l, &StepFunction::zero())?)),
                EitherOrBoth::Right((n, r)) => Ok((n.clone(), f(&StepFunction::zero(), r)?)),
                EitherOrBoth::Both((n, l), (_, r)) => Ok((n.clone(), f(l, r)?)),
            })
            .map_ok(|(n, l)| (n, l.with_max_size(ctx.max_size).with_mode(ctx.mode)))
            .try_collect()
    }

    pub fn mult(&self, lf: f32, ctx: &EvaluationContext) -> Self {
        Self {
            cdf: self.cdf_cloned(ctx),
            load: self.map_load(ctx, |l| l.mult(lf)),
        }
    }

    pub fn seq(&self, other: &Self, ctx: &EvaluationContext) -> Result<Self, CDFError> {
        Ok(Self {
            cdf: self.cdf.convolve(&other.cdf)?,
            load: self.map_loads(other, ctx, |l, r| Ok(l.add(&self.cdf.convolve_step(r)?)))?,
        })
    }

    pub fn choice(
        &self,
        my_fraction: f32,
        other: &Self,
        ctx: &EvaluationContext,
    ) -> Result<Self, CDFError> {
        Ok(Self {
            cdf: self.cdf.choice(my_fraction, &other.cdf)?,
            load: self.map_loads(other, ctx, |l, r| Ok(l.choice(my_fraction, r)))?,
        })
    }

    pub fn for_all(&self, other: &Self, ctx: &EvaluationContext) -> Result<Self, CDFError> {
        Ok(Self {
            cdf: self.cdf.for_all(&other.cdf)?,
            load: self.map_loads(other, ctx, |l, r| Ok(l.add(r)))?,
        })
    }

    pub fn for_some(&self, other: &Self, ctx: &EvaluationContext) -> Result<Self, CDFError> {
        Ok(Self {
            cdf: self.cdf.for_some(&other.cdf)?,
            load: self.map_loads(other, ctx, |l, r| Ok(l.add(r)))?,
        })
    }
}

impl Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.cdf)?;
        for (metric, load) in self.load.iter() {
            write!(f, " with {metric}{load}")?;
        }
        Ok(())
    }
}
