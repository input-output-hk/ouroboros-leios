use crate::{CDFError, CDF};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Display},
};

#[derive(Debug, PartialEq)]
pub enum DeltaQError {
    CDFError(CDFError),
    NameError(String),
    BlackBox,
}

impl std::error::Error for DeltaQError {}

impl Display for DeltaQError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeltaQError::CDFError(e) => write!(f, "CDF error: {}", e),
            DeltaQError::NameError(name) => write!(f, "Name error: {}", name),
            DeltaQError::BlackBox => write!(f, "Black box encountered"),
        }
    }
}

impl From<CDFError> for DeltaQError {
    fn from(e: CDFError) -> DeltaQError {
        DeltaQError::CDFError(e)
    }
}

#[derive(Debug, Clone, PartialEq, Default, serde::Serialize, serde::Deserialize)]
#[serde(from = "BTreeMap<String, DeltaQ>", into = "BTreeMap<String, DeltaQ>")]
pub struct EvaluationContext {
    ctx: BTreeMap<String, (DeltaQ, Option<CDF>)>,
    deps: BTreeMap<String, BTreeSet<String>>,
}

impl EvaluationContext {
    pub fn put(&mut self, name: String, delta_q: DeltaQ) {
        // first remove all computed values that depend on this name
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
        self.deps.insert(name.clone(), delta_q.deps());
        self.ctx.insert(name, (delta_q, None));
    }

    pub fn remove(&mut self, name: &str) -> Option<DeltaQ> {
        // first remove all computed values that depend on this name
        let mut to_remove = vec![name.to_owned()];
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
        self.deps.remove(name);
        self.ctx.remove(name).map(|(dq, _)| dq)
    }

    pub fn get(&self, name: &str) -> Option<&DeltaQ> {
        self.ctx.get(name).map(|(dq, _)| dq)
    }

    pub fn eval(&mut self, name: &str) -> Result<CDF, DeltaQError> {
        DeltaQ::name(name).eval(self)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&String, &DeltaQ)> {
        self.ctx.iter().map(|(k, (v, _))| (k, v))
    }
}

impl From<BTreeMap<String, DeltaQ>> for EvaluationContext {
    fn from(value: BTreeMap<String, DeltaQ>) -> Self {
        let deps = value.iter().map(|(k, v)| (k.clone(), v.deps())).collect();
        Self {
            ctx: value.into_iter().map(|(k, v)| (k, (v, None))).collect(),
            deps,
        }
    }
}

impl Into<BTreeMap<String, DeltaQ>> for EvaluationContext {
    fn into(self) -> BTreeMap<String, DeltaQ> {
        self.ctx.into_iter().map(|(k, (v, _))| (k, v)).collect()
    }
}

/// A DeltaQ is a representation of a probability distribution that can be
/// manipulated in various ways.
///
/// The Display implementation prints out the expression using the syntax from the paper:
/// - Names are printed as-is.
/// - CDFs are printed as-is.
/// - Sequences are printed as `A •->-• B`.
/// - Choices are printed as `A a⇌b B`.
/// - Universal quantifications are printed as `∀(A|B)`.
/// - Existential quantifications are printed as `∃(A|B)`.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum DeltaQ {
    /// Un unelaborated and unknown DeltaQ.
    BlackBox,
    /// A named DeltaQ that can be referenced elsewhere.
    Name(String),
    /// A CDF that is used as a DeltaQ.
    CDF(CDF),
    /// The convolution of two DeltaQs, describing the sequential execution of two outcomes.
    Seq(Box<DeltaQ>, Box<DeltaQ>),
    /// A choice between two DeltaQs (i.e. their outcomes), with a given weight of each.
    Choice(Box<DeltaQ>, f32, Box<DeltaQ>, f32),
    /// A DeltaQ that is the result of a universal quantification over two DeltaQs,
    /// meaning that both outcomes must occur.
    ForAll(Box<DeltaQ>, Box<DeltaQ>),
    /// A DeltaQ that is the result of an existential quantification over two DeltaQs,
    /// meaning that at least one of the outcomes must occur.
    ForSome(Box<DeltaQ>, Box<DeltaQ>),
}

impl Display for DeltaQ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display(f, false)
    }
}

impl DeltaQ {
    /// Create a new DeltaQ from a name, referencing a variable.
    pub fn name(name: &str) -> DeltaQ {
        DeltaQ::Name(name.to_string())
    }

    /// Create a new DeltaQ from a CDF.
    pub fn cdf(cdf: CDF) -> DeltaQ {
        DeltaQ::CDF(cdf)
    }

    /// Create a new DeltaQ from the convolution of two DeltaQs.
    pub fn seq(first: DeltaQ, second: DeltaQ) -> DeltaQ {
        DeltaQ::Seq(Box::new(first), Box::new(second))
    }

    /// Create a new DeltaQ from a choice between two DeltaQs.
    pub fn choice(first: DeltaQ, first_weight: f32, second: DeltaQ, second_weight: f32) -> DeltaQ {
        DeltaQ::Choice(
            Box::new(first),
            first_weight,
            Box::new(second),
            second_weight,
        )
    }

    /// Create a new DeltaQ from a universal quantification over two DeltaQs.
    pub fn for_all(first: DeltaQ, second: DeltaQ) -> DeltaQ {
        DeltaQ::ForAll(Box::new(first), Box::new(second))
    }

    /// Create a new DeltaQ from an existential quantification over two DeltaQs.
    pub fn for_some(first: DeltaQ, second: DeltaQ) -> DeltaQ {
        DeltaQ::ForSome(Box::new(first), Box::new(second))
    }

    pub fn deps(&self) -> BTreeSet<String> {
        match self {
            DeltaQ::BlackBox => BTreeSet::new(),
            DeltaQ::Name(name) => {
                let mut deps = BTreeSet::new();
                deps.insert(name.clone());
                deps
            }
            DeltaQ::CDF(_) => BTreeSet::new(),
            DeltaQ::Seq(first, second) => {
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
                write!(f, "■")
            }
            DeltaQ::Name(name) => {
                write!(f, "{}", name)
            }
            DeltaQ::CDF(cdf) => {
                write!(f, "{:?}", cdf)
            }
            DeltaQ::Seq(first, second) => {
                if parens {
                    write!(f, "(")?;
                }
                first.display(f, true)?;
                write!(f, " •->-• ")?;
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
                write!(f, " {}⇌{} ", first_weight, second_weight)?;
                second.display(f, true)?;
                if parens {
                    write!(f, ")")?;
                }
                Ok(())
            }
            DeltaQ::ForAll(first, second) => {
                write!(f, "∀({} | {})", first, second)
            }
            DeltaQ::ForSome(first, second) => {
                write!(f, "∃({} | {})", first, second)
            }
        }
    }

    pub fn eval(&self, ctx: &mut EvaluationContext) -> Result<CDF, DeltaQError> {
        match self {
            DeltaQ::BlackBox => Err(DeltaQError::BlackBox),
            DeltaQ::Name(n) => {
                if let Some((_, Some(cdf))) = ctx.ctx.get(n) {
                    Ok(cdf.clone())
                } else if let Some((dq, _)) = ctx.ctx.remove(n) {
                    match dq.eval(ctx) {
                        Ok(cdf) => {
                            ctx.ctx.insert(n.to_owned(), (dq, Some(cdf.clone())));
                            Ok(cdf)
                        }
                        Err(e) => {
                            ctx.ctx.insert(n.to_owned(), (dq, None));
                            Err(e)
                        }
                    }
                } else {
                    Err(DeltaQError::NameError(n.to_owned()))
                }
            }
            DeltaQ::CDF(cdf) => Ok(cdf.clone()),
            DeltaQ::Seq(first, second) => {
                let first_cdf = first.eval(ctx)?;
                let second_cdf = second.eval(ctx)?;
                first_cdf
                    .convolve(&second_cdf)
                    .map_err(DeltaQError::CDFError)
            }
            DeltaQ::Choice(first, first_fraction, second, second_fraction) => {
                let first_cdf = first.eval(ctx)?;
                let second_cdf = second.eval(ctx)?;
                first_cdf
                    .choice(
                        *first_fraction / (*first_fraction + *second_fraction),
                        &second_cdf,
                    )
                    .map_err(DeltaQError::CDFError)
            }
            DeltaQ::ForAll(first, second) => {
                let first_cdf = first.eval(ctx)?;
                let second_cdf = second.eval(ctx)?;
                first_cdf
                    .for_all(&second_cdf)
                    .map_err(DeltaQError::CDFError)
            }
            DeltaQ::ForSome(first, second) => {
                let first_cdf = first.eval(ctx)?;
                let second_cdf = second.eval(ctx)?;
                first_cdf
                    .for_some(&second_cdf)
                    .map_err(DeltaQError::CDFError)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use maplit::btreemap;

    #[test]
    fn test_display_name() {
        let dq = DeltaQ::name("A");
        assert_eq!(dq.to_string(), "A");
    }

    #[test]
    fn test_display_cdf() {
        let cdf = CDF::new(&[0.0, 0.2, 0.9], 1.0).unwrap();
        let dq = DeltaQ::cdf(cdf.clone());
        assert_eq!(dq.to_string(), format!("{:?}", cdf));
    }

    #[test]
    fn test_display_seq() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let seq = DeltaQ::seq(dq1, dq2);
        assert_eq!(seq.to_string(), "A •->-• B");
    }

    #[test]
    fn test_display_choice() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let choice = DeltaQ::choice(dq1, 0.3, dq2, 0.7);
        assert_eq!(choice.to_string(), "A 0.3⇌0.7 B");
    }

    #[test]
    fn test_display_for_all() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let for_all = DeltaQ::for_all(dq1, dq2);
        assert_eq!(for_all.to_string(), "∀(A | B)");
    }

    #[test]
    fn test_display_for_some() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let for_some = DeltaQ::for_some(dq1, dq2);
        assert_eq!(for_some.to_string(), "∃(A | B)");
    }

    #[test]
    fn test_display_nested_seq() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let dq3 = DeltaQ::name("C");
        let nested_seq = DeltaQ::seq(DeltaQ::seq(dq1, dq2), dq3);
        assert_eq!(nested_seq.to_string(), "(A •->-• B) •->-• C");
    }

    #[test]
    fn test_display_nested_choice() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let dq3 = DeltaQ::name("C");
        let nested_choice = DeltaQ::choice(DeltaQ::choice(dq1, 0.3, dq2, 0.7), 0.5, dq3, 0.5);
        assert_eq!(nested_choice.to_string(), "(A 0.3⇌0.7 B) 0.5⇌0.5 C");
    }

    #[test]
    fn test_display_nested_for_all() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let dq3 = DeltaQ::name("C");
        let dq4 = DeltaQ::name("D");
        let nested_for_all = DeltaQ::for_all(DeltaQ::for_all(dq1, dq2), DeltaQ::seq(dq3, dq4));
        assert_eq!(nested_for_all.to_string(), "∀(∀(A | B) | C •->-• D)");
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
        assert_eq!(nested_for_some.to_string(), "∃(∃(A | B) | C 1⇌2 D)");
    }

    #[test]
    fn test_scenario_from_paper_64k() {
        let ctx = btreemap! {
            "single".to_owned() =>
                DeltaQ::cdf(CDF::step(
                    &[(0.024, 1.0 / 3.0), (0.143, 2.0 / 3.0), (0.531, 1.0)],
                    0.01,
                    300,
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
        assert_eq!(result.to_string(), "CDF[(0.0200, 0.0033), (0.0400, 0.0044), (0.0600, 0.0048), (0.0800, 0.0049), (0.1000, 0.0089), (0.1400, 0.0122), (0.1600, 0.0144), (0.1800, 0.0155), (0.2000, 0.0159), (0.2200, 0.0357), (0.2800, 0.0368), (0.3000, 0.0379), (0.3200, 0.0386), (0.3400, 0.0782), (0.4200, 0.0786), (0.4400, 0.0791), (0.4600, 0.1187), (0.5300, 0.1220), (0.5500, 0.1241), (0.5600, 0.1242), (0.5700, 0.1253), (0.5800, 0.1451), (0.5900, 0.1456), (0.6100, 0.1654), (0.6700, 0.1676), (0.6900, 0.1697), (0.7000, 0.1737), (0.7100, 0.1751), (0.7300, 0.2542), (0.8100, 0.2553), (0.8300, 0.2567), (0.8500, 0.3753), (0.9500, 0.3758), (0.9700, 0.4549), (1.0600, 0.4560), (1.0800, 0.4570), (1.0900, 0.4768), (1.1000, 0.4775), (1.1200, 0.5171), (1.2000, 0.5181), (1.2200, 0.5195), (1.2400, 0.6381), (1.3400, 0.6388), (1.3600, 0.7575), (1.4800, 0.7970), (1.5900, 0.7974), (1.6100, 0.7978), (1.6300, 0.8374), (1.7300, 0.8378), (1.7500, 0.9169), (1.8700, 0.9564), (2.1200, 0.9565), (2.1400, 0.9763), (2.2600, 0.9960), (2.6500, 1.0000)]");
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
        assert_eq!(result, DeltaQError::NameError("recursive".to_owned()));
    }
}
