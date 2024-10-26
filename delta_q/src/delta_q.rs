use crate::{parser::eval_ctx, CDFError, CompactionMode, Outcome, CDF, DEFAULT_MAX_SIZE};
use smallstr::SmallString;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Display},
    str::FromStr,
    sync::Arc,
};

#[derive(Debug, PartialEq)]
pub enum DeltaQError {
    CDFError(CDFError),
    NameError(Name),
    RecursionError(Name),
    BlackBox,
}

impl std::error::Error for DeltaQError {}

impl Display for DeltaQError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeltaQError::CDFError(e) => write!(f, "CDF error: {}", e),
            DeltaQError::NameError(name) => write!(f, "Name error: {}", name),
            DeltaQError::RecursionError(name) => write!(f, "Recursion error: {}", name),
            DeltaQError::BlackBox => write!(f, "Black box encountered"),
        }
    }
}

impl From<CDFError> for DeltaQError {
    fn from(e: CDFError) -> DeltaQError {
        DeltaQError::CDFError(e)
    }
}

pub type Name = SmallString<[u8; 16]>;

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(from = "BTreeMap<String, DeltaQ>", into = "BTreeMap<Name, DeltaQ>")]
pub struct EvaluationContext {
    pub ctx: BTreeMap<Name, (DeltaQ, Option<Outcome>)>,
    pub deps: BTreeMap<Name, BTreeSet<Name>>,
    pub rec: BTreeMap<Name, Option<usize>>,
    pub max_size: usize,
    pub mode: CompactionMode,
    pub load_factor: f32,
}

impl FromStr for EvaluationContext {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        eval_ctx(s)
    }
}

impl Default for EvaluationContext {
    fn default() -> Self {
        Self {
            ctx: Default::default(),
            deps: Default::default(),
            rec: Default::default(),
            max_size: DEFAULT_MAX_SIZE,
            mode: Default::default(),
            load_factor: 1.0,
        }
    }
}

impl EvaluationContext {
    pub fn put(&mut self, name: String, delta_q: DeltaQ) {
        // first remove all computed values that depend on this name
        let name = Name::from(name);
        let mut to_remove: Vec<Name> = vec![name.clone()];
        while let Some(name) = to_remove.pop() {
            if self.ctx.get_mut(&*name).and_then(|x| x.1.take()).is_some() {
                tracing::info!("Removing computed value for {}", name);
                for (k, v) in self.deps.iter() {
                    if v.contains(&*name) {
                        to_remove.push(k.clone());
                    }
                }
            }
        }
        self.deps.insert(name.clone(), delta_q.deps());
        self.ctx.insert(name, (delta_q, None));
    }

    pub fn remove(&mut self, name: &str) -> Option<DeltaQ> {
        // first remove all computed values that depend on this name
        let name = Name::from(name);
        let mut to_remove = vec![name.clone()];
        while let Some(name) = to_remove.pop() {
            if self.ctx.get_mut(&name).and_then(|x| x.1.take()).is_some() {
                tracing::info!("Removing computed value for {}", name);
                for (k, v) in self.deps.iter() {
                    if v.contains(&name) {
                        to_remove.push(k.clone());
                    }
                }
            }
        }
        self.deps.remove(&name);
        self.ctx.remove(&name).map(|(dq, _)| dq)
    }

    pub fn get(&self, name: &str) -> Option<&DeltaQ> {
        self.ctx.get(name).map(|(dq, _)| dq)
    }

    pub fn eval(&mut self, name: &str) -> Result<Outcome, DeltaQError> {
        DeltaQ::name(name).eval(self)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Name, &DeltaQ)> {
        self.ctx.iter().map(|(k, (v, _))| (k, v))
    }
}

impl From<BTreeMap<String, DeltaQ>> for EvaluationContext {
    fn from(value: BTreeMap<String, DeltaQ>) -> Self {
        let deps = value
            .iter()
            .map(|(k, v)| (Name::from(&**k), v.deps()))
            .collect();
        Self {
            ctx: value
                .into_iter()
                .map(|(k, v)| (Name::from(k), (v, None)))
                .collect(),
            deps,
            rec: Default::default(),
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
            load_factor: 1.0,
        }
    }
}

impl Into<BTreeMap<Name, DeltaQ>> for EvaluationContext {
    fn into(self) -> BTreeMap<Name, DeltaQ> {
        self.ctx.into_iter().map(|(k, (v, _))| (k, v)).collect()
    }
}

impl Display for EvaluationContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (k, v) in self.ctx.iter() {
            writeln!(f, "{} := {}", k, v.0)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct LoadUpdate {
    pub factor: f32,
    pub summand: f32,
}

impl LoadUpdate {
    pub fn new(factor: f32, summand: f32) -> Self {
        Self { factor, summand }
    }
}

impl Display for LoadUpdate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.factor != 1.0 {
            write!(f, "×{}", self.factor)?;
        }
        if self.summand != 0.0 {
            write!(f, "+{}", self.summand)?;
        }
        Ok(())
    }
}

impl Default for LoadUpdate {
    fn default() -> Self {
        Self {
            factor: 1.0,
            summand: 0.0,
        }
    }
}

/// A DeltaQ is a representation of a probability distribution that can be
/// manipulated in various ways.
///
/// The Display implementation prints out the expression using the syntax from the paper:
/// - Names are printed as-is.
/// - CDFs are printed as-is.
/// - Sequences are printed as `A ->- B`.
/// - Choices are printed as `A a<>b B`.
/// - Universal quantifications are printed as `all(A|B)`.
/// - Existential quantifications are printed as `some(A|B)`.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum DeltaQ {
    /// Un unelaborated and unknown DeltaQ.
    BlackBox,
    /// A named DeltaQ taken from the context, with an optional recursion allowance.
    Name(Name, Option<usize>),
    /// A CDF that is used as a DeltaQ.
    Outcome(Outcome),
    /// The convolution of two DeltaQs, describing the sequential execution of two outcomes.
    Seq(
        #[serde(with = "delta_q_serde")] Arc<DeltaQ>,
        LoadUpdate,
        #[serde(with = "delta_q_serde")] Arc<DeltaQ>,
    ),
    /// A choice between two DeltaQs (i.e. their outcomes), with a given weight of each.
    Choice(
        #[serde(with = "delta_q_serde")] Arc<DeltaQ>,
        f32,
        #[serde(with = "delta_q_serde")] Arc<DeltaQ>,
        f32,
    ),
    /// A DeltaQ that is the result of a universal quantification over two DeltaQs,
    /// meaning that both outcomes must occur.
    ForAll(
        #[serde(with = "delta_q_serde")] Arc<DeltaQ>,
        #[serde(with = "delta_q_serde")] Arc<DeltaQ>,
    ),
    /// A DeltaQ that is the result of an existential quantification over two DeltaQs,
    /// meaning that at least one of the outcomes must occur.
    ForSome(
        #[serde(with = "delta_q_serde")] Arc<DeltaQ>,
        #[serde(with = "delta_q_serde")] Arc<DeltaQ>,
    ),
}

mod delta_q_serde {
    use super::DeltaQ;
    use serde::{Deserialize, Serialize};
    use std::sync::Arc;

    pub(super) fn serialize<S>(this: &Arc<DeltaQ>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        (**this).serialize(serializer)
    }

    pub(super) fn deserialize<'de, D>(deserializer: D) -> Result<Arc<DeltaQ>, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let delta_q = DeltaQ::deserialize(deserializer)?;
        Ok(Arc::new(delta_q))
    }
}

impl Display for DeltaQ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display(f, false)
    }
}

impl FromStr for DeltaQ {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        crate::parser::parse(s)
    }
}

impl DeltaQ {
    /// Create a new DeltaQ from a name, referencing a variable.
    pub fn name(name: &str) -> DeltaQ {
        DeltaQ::Name(name.into(), None)
    }

    pub fn name_rec(name: &str, rec: Option<usize>) -> DeltaQ {
        DeltaQ::Name(name.into(), rec)
    }

    /// Create a new DeltaQ from a CDF.
    pub fn cdf(cdf: CDF) -> DeltaQ {
        DeltaQ::Outcome(Outcome::new(cdf))
    }

    /// Create a new DeltaQ from the convolution of two DeltaQs.
    pub fn seq(first: DeltaQ, second: DeltaQ) -> DeltaQ {
        DeltaQ::Seq(Arc::new(first), LoadUpdate::default(), Arc::new(second))
    }

    /// Create a new DeltaQ from a choice between two DeltaQs.
    pub fn choice(first: DeltaQ, first_weight: f32, second: DeltaQ, second_weight: f32) -> DeltaQ {
        DeltaQ::Choice(
            Arc::new(first),
            first_weight,
            Arc::new(second),
            second_weight,
        )
    }

    /// Create a new DeltaQ from a universal quantification over two DeltaQs.
    pub fn for_all(first: DeltaQ, second: DeltaQ) -> DeltaQ {
        DeltaQ::ForAll(Arc::new(first), Arc::new(second))
    }

    /// Create a new DeltaQ from an existential quantification over two DeltaQs.
    pub fn for_some(first: DeltaQ, second: DeltaQ) -> DeltaQ {
        DeltaQ::ForSome(Arc::new(first), Arc::new(second))
    }

    pub fn deps(&self) -> BTreeSet<Name> {
        match self {
            DeltaQ::BlackBox => BTreeSet::new(),
            DeltaQ::Name(name, _rec) => {
                let mut deps = BTreeSet::new();
                deps.insert(name.clone());
                deps
            }
            DeltaQ::Outcome { .. } => BTreeSet::new(),
            DeltaQ::Seq(first, _load, second) => {
                let mut deps = first.deps();
                deps.extend(second.deps());
                deps
            }
            DeltaQ::Choice(first, _, second, _) => {
                let mut deps = first.deps();
                deps.extend(second.deps());
                deps
            }
            DeltaQ::ForAll(first, second) => {
                let mut deps = first.deps();
                deps.extend(second.deps());
                deps
            }
            DeltaQ::ForSome(first, second) => {
                let mut deps = first.deps();
                deps.extend(second.deps());
                deps
            }
        }
    }

    fn display(&self, f: &mut fmt::Formatter<'_>, parens: bool) -> fmt::Result {
        match self {
            DeltaQ::BlackBox => {
                write!(f, "BB")
            }
            DeltaQ::Name(name, rec) => {
                if let Some(rec) = rec {
                    write!(f, "{}^{}", name, rec)
                } else {
                    write!(f, "{}", name)
                }
            }
            DeltaQ::Outcome(outcome) => {
                write!(f, "{}", outcome)
            }
            DeltaQ::Seq(first, load, second) => {
                if parens {
                    write!(f, "(")?;
                }
                first.display(f, true)?;
                write!(f, " ->-{load} ")?;
                second.display(f, true)?;
                if parens {
                    write!(f, ")")?;
                }
                Ok(())
            }
            DeltaQ::Choice(first, first_weight, second, second_weight) => {
                if parens {
                    write!(f, "(")?;
                }
                first.display(f, true)?;
                write!(f, " {}<>{} ", first_weight, second_weight)?;
                second.display(f, true)?;
                if parens {
                    write!(f, ")")?;
                }
                Ok(())
            }
            DeltaQ::ForAll(first, second) => {
                write!(f, "all({} | {})", first, second)
            }
            DeltaQ::ForSome(first, second) => {
                write!(f, "some({} | {})", first, second)
            }
        }
    }

    pub fn eval(&self, ctx: &mut EvaluationContext) -> Result<Outcome, DeltaQError> {
        match self {
            DeltaQ::BlackBox => Err(DeltaQError::BlackBox),
            DeltaQ::Name(n, r) => {
                // recursion is only allowed if not yet recursing on this name or there is an existing allowance
                // which means that a new allowance leads to error if there is an existing one (this would permit
                // infinite recursion)
                //
                // None means not recursing on this name
                // Some(None) means recursing on this name without allowance
                // Some(Some(n)) means recursing on this name with n as the remaining allowance
                let recursion = if let Some(r) = r {
                    if ctx.rec.contains_key(n) {
                        return Err(DeltaQError::RecursionError(n.to_owned()));
                    }
                    Some(ctx.rec.entry(n.to_owned()).or_insert(Some(*r)).as_mut())
                } else {
                    ctx.rec.get_mut(n).map(|r| r.as_mut())
                };
                if let Some(Some(allowance)) = recursion {
                    match ctx.ctx.get(n) {
                        Some((dq, _)) => {
                            let mut increment = true;
                            let ret = if *allowance == 0 {
                                increment = false;
                                Ok(Outcome {
                                    cdf: CDF::from_steps(&[(0.0, 1.0)]).unwrap(),
                                    load: BTreeMap::new(),
                                })
                            } else {
                                *allowance -= 1;
                                dq.clone().eval(ctx)
                            };
                            if r.is_some() {
                                ctx.rec.remove(n);
                            } else if increment {
                                *ctx.rec.get_mut(n).unwrap().as_mut().unwrap() += 1;
                            }
                            ret
                        }
                        None => Err(DeltaQError::NameError(n.to_owned())),
                    }
                } else if recursion.is_some() {
                    Err(DeltaQError::RecursionError(n.to_owned()))
                } else {
                    match ctx.ctx.get(n) {
                        Some((_, Some(cdf))) if ctx.load_factor == 1.0 => Ok(cdf.clone()),
                        Some((dq, _)) => {
                            ctx.rec.insert(n.to_owned(), None);
                            let cdf = dq.clone().eval(ctx);
                            ctx.rec.remove(n);
                            let cdf = cdf?;
                            if ctx.load_factor == 1.0 {
                                ctx.ctx.get_mut(n).unwrap().1 = Some(cdf.clone());
                            }
                            Ok(cdf)
                        }
                        None => Err(DeltaQError::NameError(n.to_owned())),
                    }
                }
            }
            DeltaQ::Outcome(outcome) => Ok(outcome.mult(ctx.load_factor, ctx)),
            DeltaQ::Seq(first, load, second) => {
                let first_cdf = first.eval(ctx)?;
                let lf = ctx.load_factor;
                ctx.load_factor = ctx.load_factor * load.factor + load.summand;
                let second_cdf = second.eval(ctx)?;
                ctx.load_factor = lf;
                first_cdf
                    .seq(&second_cdf, ctx)
                    .map_err(DeltaQError::CDFError)
            }
            DeltaQ::Choice(first, first_fraction, second, second_fraction) => {
                let first_cdf = first.eval(ctx)?;
                let second_cdf = second.eval(ctx)?;
                first_cdf
                    .choice(
                        *first_fraction / (*first_fraction + *second_fraction),
                        &second_cdf,
                        ctx,
                    )
                    .map_err(DeltaQError::CDFError)
            }
            DeltaQ::ForAll(first, second) => {
                let first_cdf = first.eval(ctx)?;
                let second_cdf = second.eval(ctx)?;
                first_cdf
                    .for_all(&second_cdf, ctx)
                    .map_err(DeltaQError::CDFError)
            }
            DeltaQ::ForSome(first, second) => {
                let first_cdf = first.eval(ctx)?;
                let second_cdf = second.eval(ctx)?;
                first_cdf
                    .for_some(&second_cdf, ctx)
                    .map_err(DeltaQError::CDFError)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        parser::{eval_ctx, outcome},
        StepFunction,
    };
    use maplit::btreemap;
    use winnow::Parser;

    #[test]
    fn test_display_name() {
        let dq = DeltaQ::name("A");
        assert_eq!(dq.to_string(), "A");
        assert_eq!(dq, "A".parse().unwrap());
    }

    #[test]
    fn test_display_cdf() {
        let cdf = CDF::new(&[0.0, 0.2, 0.9], 1.0).unwrap();
        let dq = DeltaQ::cdf(cdf.clone());
        assert_eq!(dq.to_string(), "CDF[(1, 0.2), (2, 0.9)]");
        assert_eq!(dq, "CDF[(1, 0.2), (2, 0.9)]".parse().unwrap());
    }

    #[test]
    fn test_display_seq() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let seq = DeltaQ::seq(dq1, dq2);
        assert_eq!(seq.to_string(), "A ->- B");
        assert_eq!(seq, "A ->- B".parse().unwrap());
    }

    #[test]
    fn test_display_choice() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let choice = DeltaQ::choice(dq1, 0.3, dq2, 0.7);
        assert_eq!(choice.to_string(), "A 0.3<>0.7 B");
        assert_eq!(choice, "A 0.3<>0.7 B".parse().unwrap());
    }

    #[test]
    fn test_display_for_all() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let for_all = DeltaQ::for_all(dq1, dq2);
        assert_eq!(for_all.to_string(), "all(A | B)");
        assert_eq!(for_all, "all(A | B)".parse().unwrap());
    }

    #[test]
    fn test_display_for_some() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let for_some = DeltaQ::for_some(dq1, dq2);
        assert_eq!(for_some.to_string(), "some(A | B)");
        assert_eq!(for_some, "some(A | B)".parse().unwrap());
    }

    #[test]
    fn test_display_nested_seq() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let dq3 = DeltaQ::name("C");
        let nested_seq = DeltaQ::seq(DeltaQ::seq(dq1, dq2), dq3);
        assert_eq!(nested_seq.to_string(), "(A ->- B) ->- C");
        assert_eq!(nested_seq, "(A ->- B) ->- C".parse().unwrap());
        assert_eq!(nested_seq, "A ->- B ->- C".parse().unwrap());
    }

    #[test]
    fn test_display_nested_choice() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let dq3 = DeltaQ::name("C");
        let nested_choice = DeltaQ::choice(dq1, 0.3, DeltaQ::choice(dq2, 0.5, dq3, 0.5), 0.7);
        assert_eq!(nested_choice.to_string(), "A 0.3<>0.7 (B 0.5<>0.5 C)");
        assert_eq!(nested_choice, "A 0.3<>0.7 (B 0.5<>0.5 C)".parse().unwrap());
        assert_eq!(nested_choice, "A 0.3<>0.7 B 0.5<>0.5 C".parse().unwrap());
    }

    #[test]
    fn test_display_nested_for_all() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let dq3 = DeltaQ::name("C");
        let dq4 = DeltaQ::name("D");
        let nested_for_all = DeltaQ::for_all(DeltaQ::for_all(dq1, dq2), DeltaQ::seq(dq3, dq4));
        assert_eq!(nested_for_all.to_string(), "all(all(A | B) | C ->- D)");
        assert_eq!(nested_for_all, "all(all(A | B) | C ->- D)".parse().unwrap());
    }

    #[test]
    fn test_display_nested_for_some() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let dq3 = DeltaQ::name("C");
        let dq4 = DeltaQ::name("D");
        let nested_for_some = DeltaQ::for_some(
            DeltaQ::for_some(dq1, dq2),
            DeltaQ::choice(dq3, 1.0, dq4, 2.0),
        );
        assert_eq!(nested_for_some.to_string(), "some(some(A | B) | C 1<>2 D)");
        assert_eq!(
            nested_for_some,
            "some(some(A | B) | C 1<>2 D)".parse().unwrap()
        );
    }

    #[test]
    fn test_scenario_from_paper_64k() {
        let ctx = btreemap! {
            "single".to_owned() =>
                DeltaQ::cdf(CDF::from_steps(
                    &[(0.024, 1.0 / 3.0), (0.143, 2.0 / 3.0), (0.531, 1.0)],
                )
                .unwrap()),
            "model2".to_owned() =>
                DeltaQ::choice(
                    DeltaQ::name("single"),
                    1.0,
                    DeltaQ::seq(DeltaQ::name("single"), DeltaQ::name("single")),
                    100.0,
                ),
            "model3".to_owned() =>
                DeltaQ::choice(
                    DeltaQ::name("single"),
                    1.0,
                    DeltaQ::seq(DeltaQ::name("single"), DeltaQ::name("model2")),
                    100.0,
                ),
            "model4".to_owned() =>
                DeltaQ::choice(
                    DeltaQ::name("single"),
                    1.0,
                    DeltaQ::seq(DeltaQ::name("single"), DeltaQ::name("model3")),
                    100.0,
                ),
            "model5".to_owned() =>
                DeltaQ::choice(
                    DeltaQ::name("single"),
                    1.0,
                    DeltaQ::seq(DeltaQ::name("single"), DeltaQ::name("model4")),
                    100.0,
                ),
        };
        let result = DeltaQ::name("model5").eval(&mut ctx.into()).unwrap();
        assert_eq!(result.to_string(), "CDF[(0.024, 0.0033), (0.048, 0.00439), (0.072, 0.00475), (0.096, 0.00487), (0.12, 0.00882), (0.143, 0.01212), (0.167, 0.0143), (0.191, 0.01538), (0.215, 0.01585), (0.239, 0.03563), (0.286, 0.03672), (0.31, 0.03779), (0.334, 0.03851), (0.358, 0.07805), (0.429, 0.07841), (0.453, 0.07889), (0.477, 0.11843), (0.531, 0.12173), (0.555, 0.12391), (0.572, 0.12403), (0.579, 0.12511), (0.596, 0.14488), (0.603, 0.14536), (0.627, 0.16513), (0.674, 0.16731), (0.698, 0.16947), (0.715, 0.17342), (0.722, 0.17484), (0.746, 0.25394), (0.817, 0.25502), (0.841, 0.25644), (0.865, 0.37508), (0.96, 0.37555), (0.984, 0.45465), (1.062, 0.45574), (1.086, 0.45681), (1.103, 0.47659), (1.11, 0.4773), (1.134, 0.51685), (1.205, 0.51792), (1.229, 0.51935), (1.253, 0.63799), (1.348, 0.6387), (1.372, 0.75734), (1.491, 0.79689), (1.593, 0.79725), (1.617, 0.79772), (1.641, 0.83727), (1.736, 0.83774), (1.76, 0.91683), (1.879, 0.95638), (2.124, 0.9565), (2.148, 0.97627), (2.267, 0.99605), (2.655, 1)]");
    }

    #[test]
    fn test_recursive_deltaq() {
        let ctx = btreemap! {
            "recursive".to_owned() =>
                DeltaQ::choice(
                    DeltaQ::name("base"),
                    1.0,
                    DeltaQ::seq(DeltaQ::name("base"), DeltaQ::name("recursive")),
                    1.0,
                ),
            "base".to_owned() => DeltaQ::cdf(CDF::new(&[0.0, 0.5, 1.0], 1.0).unwrap()),
        };
        let result = DeltaQ::name("recursive").eval(&mut ctx.into()).unwrap_err();
        assert_eq!(result, DeltaQError::RecursionError("recursive".into()));
    }

    #[test]
    fn parse_cdf() {
        let res = "CDF[(2, 0.2), (2, 0.9)]".parse::<DeltaQ>().unwrap_err();
        assert!(res.contains("non-monotonic"), "{}", res);

        let res = "CDF[(2a, 0.2), (2, 0.9)]".parse::<DeltaQ>().unwrap_err();
        assert!(res.contains("CDF"), "{}", res);

        let res = "+a".parse::<DeltaQ>().unwrap_err();
        assert!(
            res.contains("expected 'BB', name, CDF, 'all(', 'some(', or parentheses"),
            "{}",
            res
        );
    }

    #[test]
    fn parse_outcome() {
        let expected = Outcome::new(CDF::from_steps(&[(1.0, 0.1), (2.0, 0.3)]).unwrap()).with_load(
            "metric".into(),
            StepFunction::new(&[(0.0, 12.0), (1.5, 0.0)]).unwrap(),
        );
        assert_eq!(
            DeltaQ::Outcome(expected),
            "CDF[(1, 0.1), (2, 0.3)] WITH metric[(0, 12), (1.5, 0)]"
                .parse::<DeltaQ>()
                .unwrap()
        );
    }

    #[test]
    fn parse_load_update() {
        let res = "BB ->-*3+4 BB".parse::<DeltaQ>().unwrap();
        assert_eq!(
            res,
            DeltaQ::Seq(
                Arc::new(DeltaQ::BlackBox),
                LoadUpdate::new(3.0, 4.0),
                Arc::new(DeltaQ::BlackBox)
            )
        );
        assert_eq!(res.to_string(), "BB ->-×3+4 BB");
    }

    #[test]
    fn test_recursion() {
        let mut ctx = EvaluationContext::default();

        ctx.put("f".to_owned(), "CDF[(1,1)] ->- f ->- f".parse().unwrap());
        let res = DeltaQ::Name("f".into(), Some(3)).eval(&mut ctx).unwrap();
        assert_eq!(DeltaQ::Outcome(res), outcome.parse("CDF[(7,1)]").unwrap());

        ctx.put("f".to_owned(), "CDF[(1,1)] ->- f".parse().unwrap());
        for i in 0..10 {
            let res = DeltaQ::Name("f".into(), Some(i)).eval(&mut ctx).unwrap();
            assert_eq!(
                DeltaQ::Outcome(res),
                outcome.parse(&format!("CDF[({i},1)]")).unwrap()
            );
        }

        ctx.put(
            "cdf".to_owned(),
            "CDF[(0.1, 0.33), (0.2, 0.66), (0.4, 1)]".parse().unwrap(),
        );
        ctx.put(
            "out".to_owned(),
            "cdf ->- (cdf 0.5<>3 all(cdf | cdf ->- out))"
                .parse()
                .unwrap(),
        );
        let res = DeltaQ::Name("out".into(), Some(1)).eval(&mut ctx).unwrap();
        assert_eq!(
            res.cdf,
            CDF::from_steps(&[
                (0.2, 0.046360295),
                (0.3, 0.20068718),
                (0.4, 0.30865377),
                (0.5, 0.53209203),
                (0.6, 0.81900346),
                (0.8, 1.0)
            ])
            .unwrap()
        );
    }

    #[test]
    fn parse_eval_ctx() {
        const SOURCE: &'static str = "
            -- start with a comment
            diffuse := -- add a comment here
            hop 0.6<>99.4 ((hop ->- hop) 8.58<>90.82 (((hop ->- hop) ->- hop) 65.86<>24.96 (((hop ->- hop) ->- hop) ->- hop)))

            diffuseEB :=
            hopEB 0.6<>99.4 ((hopEB ->- hopEB) 8.58<>90.82 (((hopEB ->- hopEB) ->- hopEB) 65.86<>24.96 (((hopEB ->- hopEB) ->- hopEB) ->- hopEB)))

            far :=
            CDF[(0.268, 1)]

            farL :=
            CDF[(0.531, 1)]

            farXL :=
            CDF[(1.598, 1)]

            hop :=
            (((near ->- near) ->- near) ->- nearXL) 1<>2 ((((mid ->- mid) ->- mid) ->- midXL) 1<>1 (((far ->- far) ->- far) ->- farXL))

            hopEB :=
            (((near ->- near) ->- near) ->- nearL) 1<>2 ((((mid ->- mid) ->- mid) ->- midL) 1<>1 (((far ->- far) ->- far) ->- farL))

            mid :=
            CDF[(0.069, 1)]

            midL :=
            CDF[(0.143, 1)]

            midXL :=
            CDF[(0.404, 1)]

            near :=
            CDF[(0.012, 1)]

            nearL :=
            CDF[(0.024, 1)]

            nearXL :=
            CDF[(0.078, 1)]
            ";
        let ctx = eval_ctx(SOURCE).unwrap();
        assert_eq!(ctx.iter().count(), 13);
        assert_eq!(ctx.get("diffuse").unwrap().to_string(), "hop 0.6<>99.4 ((hop ->- hop) 8.58<>90.82 (((hop ->- hop) ->- hop) 65.86<>24.96 (((hop ->- hop) ->- hop) ->- hop)))");

        const DEST: &'static str = "\
            diffuse := hop 0.6<>99.4 ((hop ->- hop) 8.58<>90.82 (((hop ->- hop) ->- hop) 65.86<>24.96 (((hop ->- hop) ->- hop) ->- hop)))\n\
            diffuseEB := hopEB 0.6<>99.4 ((hopEB ->- hopEB) 8.58<>90.82 (((hopEB ->- hopEB) ->- hopEB) 65.86<>24.96 (((hopEB ->- hopEB) ->- hopEB) ->- hopEB)))\nfar := CDF[(0.268, 1)]\n\
            farL := CDF[(0.531, 1)]\n\
            farXL := CDF[(1.598, 1)]\n\
            hop := (((near ->- near) ->- near) ->- nearXL) 1<>2 ((((mid ->- mid) ->- mid) ->- midXL) 1<>1 (((far ->- far) ->- far) ->- farXL))\n\
            hopEB := (((near ->- near) ->- near) ->- nearL) 1<>2 ((((mid ->- mid) ->- mid) ->- midL) 1<>1 (((far ->- far) ->- far) ->- farL))\n\
            mid := CDF[(0.069, 1)]\n\
            midL := CDF[(0.143, 1)]\n\
            midXL := CDF[(0.404, 1)]\n\
            near := CDF[(0.012, 1)]\n\
            nearL := CDF[(0.024, 1)]\n\
            nearXL := CDF[(0.078, 1)]\n";
        assert_eq!(ctx.to_string(), DEST);
    }

    #[test]
    fn test_load_update() {
        let outcome = Outcome::new(CDF::from_steps(&[(1.5, 0.1)]).unwrap()).with_load(
            "net".into(),
            StepFunction::new(&[(0.0, 12.0), (1.0, 0.0)]).unwrap(),
        );
        let dq = DeltaQ::Seq(
            Arc::new(DeltaQ::Outcome(outcome.clone())),
            LoadUpdate::new(2.0, 0.0),
            Arc::new(DeltaQ::Outcome(outcome)),
        );
        assert_eq!(dq.to_string(), "CDF[(1.5, 0.1)] WITH net[(0, 12), (1, 0)] ->-×2 CDF[(1.5, 0.1)] WITH net[(0, 12), (1, 0)]");
        let mut ctx = EvaluationContext::default();
        let res = dq.eval(&mut ctx).unwrap();
        let expected = Outcome::new(CDF::from_steps(&[(3.0, 0.010000001)]).unwrap()).with_load(
            "net".into(),
            StepFunction::new(&[(0.0, 12.0), (1.0, 0.0), (1.5, 2.4), (2.5, 0.0)]).unwrap(),
        );
        assert_eq!(res, expected);
    }

    #[test]
    fn distributive_choice() {
        let mut ctx = eval_ctx("\
            a := CDF[(1, 0.4), (2, 1)] WITH common[(0.1, 3), (0.8, 0)] WITH a[(0,1), (1,0)] WITH ab[(0, 12), (1,0)]
            b := CDF[(2, 0.5), (3, 1)] WITH common[(0.2, 0.1), (1.2, 0.2), (1.5, 0)] WITH b[(0,1), (2,0)] WITH ab[(0, 7), (2,0)]
            c := CDF[(3, 0.6), (4, 1)] WITH common[(2.4, 100), (2.5, 0)] WITH c[(0,1), (3,0)]

            e1 := a ->- b 1<>2 a ->- c
            e2 := a ->- (b 1<>2 c)
            ").unwrap();
        let e1 = DeltaQ::name("e1").eval(&mut ctx).unwrap();
        let e2 = DeltaQ::name("e2").eval(&mut ctx).unwrap();
        assert!(e1.similar(&e2), "{e1}\ndoes not match\n{e2}");

        let mut ctx = eval_ctx("\
            a := CDF[(1, 0.4), (2, 1)] WITH common[(0.1, 3), (0.8, 0)] WITH a[(0,1), (1,0)] WITH ab[(0, 12), (1,0)]
            b := CDF[(2, 0.5), (3, 1)] WITH common[(0.2, 0.1), (1.2, 0.2), (1.5, 0)] WITH b[(0,1), (2,0)] WITH ab[(0, 7), (2,0)]
            c := CDF[(3, 0.6), (4, 1)] WITH common[(2.4, 100), (2.5, 0)] WITH c[(0,1), (3,0)]

            e1 := a ->-×3 b 1<>2 a ->-×3 c
            e2 := a ->-×3 (b 1<>2 c)
            ").unwrap();
        let e1 = DeltaQ::name("e1").eval(&mut ctx).unwrap();
        let e2 = DeltaQ::name("e2").eval(&mut ctx).unwrap();
        assert!(e1.similar(&e2), "{e1}\ndoes not match\n{e2}");
    }
}
