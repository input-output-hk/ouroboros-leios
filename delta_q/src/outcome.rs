use crate::{delta_q::Name, CDFError, PersistentContext, StepFunction, CDF};
use itertools::{EitherOrBoth, Itertools};
use std::{
    collections::BTreeMap,
    fmt::{self, Display},
};

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Outcome {
    pub cdf: CDF,
    pub load: BTreeMap<Name, StepFunction<CDF>>,
}

impl Outcome {
    pub fn new(cdf: CDF) -> Self {
        Self {
            cdf,
            load: BTreeMap::new(),
        }
    }

    pub fn top() -> Self {
        Self::new(CDF::top())
    }

    pub fn new_with_load(cdf: CDF, load: BTreeMap<Name, StepFunction>) -> Self {
        let load = load
            .into_iter()
            .map(|(n, l)| (n, l.map(|y| CDF::new(&[(*y, 1.0)]).unwrap())))
            .collect();
        Self { cdf, load }
    }

    pub fn cdf(&self) -> &CDF {
        &self.cdf
    }

    pub fn load(&self) -> &BTreeMap<Name, StepFunction<CDF>> {
        &self.load
    }

    pub fn with_load(mut self, metric: Name, load: StepFunction<CDF>) -> Self {
        self.load.insert(metric, load);
        self
    }

    fn cdf_cloned(&self, ctx: &PersistentContext) -> CDF {
        self.cdf
            .clone()
            .with_max_size(ctx.max_size)
            .with_mode(ctx.mode)
    }

    fn map_load(
        &self,
        ctx: &PersistentContext,
        f: impl Fn(&StepFunction<CDF>) -> StepFunction<CDF>,
    ) -> BTreeMap<Name, StepFunction<CDF>> {
        self.load
            .iter()
            .map(|(n, l)| {
                (
                    n.clone(),
                    f(l).with_max_size(ctx.max_size).with_mode(ctx.mode),
                )
            })
            .collect()
    }

    fn map_loads(
        &self,
        other: &Self,
        ctx: &PersistentContext,
        f: impl Fn(&StepFunction<CDF>, &StepFunction<CDF>) -> Result<StepFunction<CDF>, CDFError>,
    ) -> Result<BTreeMap<Name, StepFunction<CDF>>, CDFError> {
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

    pub fn mult(&self, lf: f32, ctx: &PersistentContext) -> Self {
        Self {
            cdf: self.cdf_cloned(ctx),
            load: self.map_load(ctx, |l| l.scale(lf)),
        }
    }

    pub fn seq(&self, other: &Self, ctx: &PersistentContext) -> Self {
        Self {
            cdf: self.cdf.convolve(&other.cdf),
            load: self
                .map_loads(other, ctx, |l, r| Ok(l.sum_up(&self.cdf.convolve_step(r))))
                .expect("infallible"),
        }
    }

    pub fn choice(
        &self,
        my_fraction: f32,
        other: &Self,
        ctx: &PersistentContext,
    ) -> Result<Self, CDFError> {
        Ok(Self {
            cdf: self.cdf.choice(my_fraction, &other.cdf)?,
            load: self.map_loads(other, ctx, |l, r| Ok(l.choice(my_fraction, r)?))?,
        })
    }

    pub fn for_all(&self, other: &Self, ctx: &PersistentContext) -> Self {
        Self {
            cdf: self.cdf.for_all(&other.cdf),
            load: self
                .map_loads(other, ctx, |l, r| Ok(l.sum_up(r)))
                .expect("infallible"),
        }
    }

    pub fn for_some(&self, other: &Self, ctx: &PersistentContext) -> Self {
        Self {
            cdf: self.cdf.for_some(&other.cdf),
            load: self
                .map_loads(other, ctx, |l, r| Ok(l.sum_up(r)))
                .expect("infallible"),
        }
    }

    pub fn similar(&self, other: &Self) -> bool {
        self.cdf.steps().similar(&other.cdf.steps())
            && self
                .load
                .iter()
                .merge_join_by(other.load.iter(), |(nl, _), (nr, _)| nl.cmp(nr))
                .all(|x| match x {
                    EitherOrBoth::Both((_, l), (_, r)) => l.similar(r),
                    _ => false,
                })
    }
}
impl Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.cdf)?;
        for (metric, load) in self.load.iter() {
            write!(f, " WITH {metric}{load}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use maplit::btreemap;

    fn outcomes() -> (Outcome, Outcome) {
        let outcome1 = Outcome::new_with_load(
            CDF::new(&[(1.0, 0.4), (2.0, 1.0)]).unwrap(),
            btreemap! {
                "m1".into() => StepFunction::new(&[(0.1, 15.0), (0.5, 10.0), (1.9, 0.0)]).unwrap(),
                "m2".into() => StepFunction::new(&[(1.5, 100.0), (2.0, 0.0)]).unwrap(),
            },
        );
        let outcome2 = Outcome::new_with_load(
            CDF::new(&[(0.0, 0.1), (5.0, 1.0)]).unwrap(),
            btreemap! {
                "m2".into() => StepFunction::new(&[(0.0, 50.0), (4.5, 0.0)]).unwrap(),
                "m3".into() => StepFunction::new(&[(4.5, 12.0), (5.5, 0.0)]).unwrap(),
            },
        );
        (outcome1, outcome2)
    }

    #[test]
    fn test_choice() {
        let ctx = PersistentContext::default();
        let (outcome1, outcome2) = outcomes();
        let res = outcome1.choice(0.6, &outcome2, &ctx).unwrap();
        assert_eq!(res.to_string(), "CDF[(0, 0.04), (1, 0.28), (2, 0.64), (5, 1)] \
            WITH m1[(0.1, CDF[(0, 0.4), (15, 1)]), (0.5, CDF[(0, 0.4), (10, 1)]), (1.9, 0)] \
            WITH m2[(0, CDF[(0, 0.6), (50, 1)]), (1.5, CDF[(50, 0.4), (100, 1)]), (2, CDF[(0, 0.6), (50, 1)]), (4.5, 0)] \
            WITH m3[(4.5, CDF[(0, 0.6), (12, 1)]), (5.5, 0)]");
    }

    #[test]
    fn test_for_all() {
        let ctx = PersistentContext::default();
        let (outcome1, outcome2) = outcomes();
        let res = outcome1.for_all(&outcome2, &ctx);
        assert_eq!(
            res.to_string(),
            "CDF[(1, 0.04), (2, 0.1), (5, 1)] \
            WITH m1[(0.1, 15), (0.5, 10), (1.9, 0)] \
            WITH m2[(0, 50), (1.5, 150), (2, 50), (4.5, 0)] \
            WITH m3[(4.5, 12), (5.5, 0)]"
        );
    }

    #[test]
    fn test_for_some() {
        let ctx = PersistentContext::default();
        let (outcome1, outcome2) = outcomes();
        let res = outcome1.for_some(&outcome2, &ctx);
        assert_eq!(
            res.to_string(),
            "CDF[(0, 0.1), (1, 0.46), (2, 1)] \
            WITH m1[(0.1, 15), (0.5, 10), (1.9, 0)] \
            WITH m2[(0, 50), (1.5, 150), (2, 50), (4.5, 0)] \
            WITH m3[(4.5, 12), (5.5, 0)]"
        );
    }

    #[test]
    fn test_seq() {
        let ctx = PersistentContext::default();
        let (outcome1, outcome2) = outcomes();
        let res = outcome1.seq(&outcome2, &ctx);
        assert_eq!(
            res.to_string(),
            "CDF[(1, 0.04), (2, 0.1), (6, 0.46), (7, 1)] \
            WITH m1[(0.1, 15), (0.5, 10), (1.9, 0)] \
            WITH m2[(1, CDF[(0, 0.6), (50, 1)]), (1.5, CDF[(100, 0.6), (150, 1)]), (2, 50), (5.5, CDF[(0, 0.4), (50, 1)]), (6.5, 0)] \
            WITH m3[(5.5, CDF[(0, 0.6), (12, 1)]), (6.5, CDF[(0, 0.4), (12, 1)]), (7.5, 0)]"
        );
    }
}
