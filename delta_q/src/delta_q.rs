use crate::{parser::eval_ctx, CDFError, CompactionMode, Outcome, CDF, DEFAULT_MAX_SIZE};
use itertools::Itertools;
use smallstr::SmallString;
use std::{
    cell::{Cell, OnceCell, RefCell},
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Display},
    str::FromStr,
    sync::{Arc, OnceLock},
};

#[derive(Debug, Clone, PartialEq)]
pub enum DeltaQError {
    CDFError(CDFError),
    NameError(Name),
    RecursionError(Name),
    BlackBox,
    TooManySteps,
    EvaluationError,
}

impl std::error::Error for DeltaQError {}

impl Display for DeltaQError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeltaQError::CDFError(e) => write!(f, "CDF error: {}", e),
            DeltaQError::NameError(name) => write!(f, "Name error: {}", name),
            DeltaQError::RecursionError(name) => write!(f, "Recursion error: {}", name),
            DeltaQError::BlackBox => write!(f, "Black box encountered"),
            DeltaQError::TooManySteps => write!(f, "Too many steps in gossip expansion"),
            DeltaQError::EvaluationError => write!(f, "Evaluation error"),
        }
    }
}

impl From<CDFError> for DeltaQError {
    fn from(e: CDFError) -> DeltaQError {
        DeltaQError::CDFError(e)
    }
}

pub type Name = SmallString<[u8; 16]>;

// Update EvaluationContext to contain only static data
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct PersistentContext {
    pub ctx: BTreeMap<Name, (DeltaQ, Option<Name>)>,
    pub order: Vec<Name>,
    pub max_size: usize,
    pub mode: CompactionMode,
}

impl FromStr for PersistentContext {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        eval_ctx(s)
    }
}

impl Default for PersistentContext {
    fn default() -> Self {
        Self {
            ctx: Default::default(),
            order: Vec::new(),
            max_size: DEFAULT_MAX_SIZE,
            mode: Default::default(),
        }
    }
}

impl PersistentContext {
    pub fn put(&mut self, name: String, delta_q: DeltaQ) {
        let name = Name::from(name);
        let existed = self.ctx.insert(name.clone(), (delta_q, None)).is_some();
        if !existed {
            self.order.push(name);
        }
    }

    pub fn put_comment(&mut self, comment: &str) {
        self.order.push(Name::from(comment));
    }

    pub fn remove(&mut self, name: &str) -> Option<DeltaQ> {
        self.ctx.remove(name).map(|(dq, _)| dq)
    }

    pub fn get(&self, name: &str) -> Option<&DeltaQ> {
        self.ctx.get(name).map(|(dq, _)| dq)
    }

    pub fn eval(&self, name: &str) -> Result<Outcome, DeltaQError> {
        DeltaQ::name(name).eval(self, &mut EphemeralContext::default())
    }

    pub fn iter(&self) -> impl Iterator<Item = &Name> {
        self.order.iter()
    }

    pub fn constraint(&self, name: &str) -> Option<&Name> {
        self.ctx.get(name).and_then(|(_, c)| c.as_ref())
    }

    pub fn set_constraint(&mut self, name: &str, constraint: Option<Name>) {
        if let Some((_, c)) = self.ctx.get_mut(name) {
            *c = constraint;
        }
    }

    pub fn constraints(&self) -> impl Iterator<Item = (&Name, &Name)> {
        self.ctx
            .iter()
            .filter_map(|(k, (_, c))| c.as_ref().map(|c| (k, c)))
    }
}

#[cfg(test)]
impl From<BTreeMap<String, DeltaQ>> for PersistentContext {
    fn from(value: BTreeMap<String, DeltaQ>) -> Self {
        Self {
            ctx: value
                .into_iter()
                .map(|(k, v)| (Name::from(k), (v, None)))
                .collect(),
            order: Vec::new(),
            max_size: DEFAULT_MAX_SIZE,
            mode: CompactionMode::default(),
        }
    }
}

#[cfg(test)]
impl Into<BTreeMap<Name, DeltaQ>> for PersistentContext {
    fn into(self) -> BTreeMap<Name, DeltaQ> {
        self.ctx.into_iter().map(|(k, (v, _))| (k, v)).collect()
    }
}

impl Display for PersistentContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for k in self.iter() {
            let Some((v, c)) = self.ctx.get(k) else {
                write!(f, "{}", k)?;
                continue;
            };
            if let Some(c) = c {
                writeln!(f, "{} >= {} := {}", k, c, v)?;
            } else {
                writeln!(f, "{} := {}", k, v)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct LoadUpdate {
    pub factor: f32,
    pub disjoint_names: BTreeSet<Name>,
}

impl LoadUpdate {
    pub fn new(factor: f32) -> Self {
        Self {
            factor,
            disjoint_names: BTreeSet::default(),
        }
    }
}

impl Display for LoadUpdate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.disjoint_names.is_empty() {
            write!(f, "{}", self.disjoint_names.iter().join(", "))?;
        }
        if self.factor != 1.0 {
            write!(f, "×{}", self.factor)?;
        }
        Ok(())
    }
}

impl Default for LoadUpdate {
    fn default() -> Self {
        Self {
            factor: 1.0,
            disjoint_names: BTreeSet::default(),
        }
    }
}

/// A DeltaQ is a representation of a probability distribution that can be
/// manipulated in various ways.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct DeltaQ {
    #[serde(with = "delta_q_serde")]
    expr: Arc<DeltaQExpr>,
    #[serde(skip)]
    expanded: OnceCell<Result<Arc<DeltaQExpr>, DeltaQError>>,
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum DeltaQExpr {
    /// Un unelaborated and unknown DeltaQ.
    BlackBox,
    /// A named DeltaQ taken from the context, with an optional recursion allowance.
    Name(Name, Option<usize>),
    /// A CDF that is used as a DeltaQ.
    Outcome(Outcome),
    /// The convolution of two DeltaQs, describing the sequential execution of two outcomes.
    Seq(
        #[serde(with = "delta_q_serde")] Arc<DeltaQExpr>,
        LoadUpdate,
        #[serde(with = "delta_q_serde")] Arc<DeltaQExpr>,
    ),
    /// A choice between two DeltaQs (i.e. their outcomes), with a given weight of each.
    Choice(
        #[serde(with = "delta_q_serde")] Arc<DeltaQExpr>,
        f32,
        #[serde(with = "delta_q_serde")] Arc<DeltaQExpr>,
        f32,
    ),
    /// A DeltaQ that is the result of a universal quantification over two DeltaQs,
    /// meaning that both outcomes must occur.
    ForAll(
        #[serde(with = "delta_q_serde")] Arc<DeltaQExpr>,
        #[serde(with = "delta_q_serde")] Arc<DeltaQExpr>,
    ),
    /// A DeltaQ that is the result of an existential quantification over two DeltaQs,
    /// meaning that at least one of the outcomes must occur.
    ForSome(
        #[serde(with = "delta_q_serde")] Arc<DeltaQExpr>,
        #[serde(with = "delta_q_serde")] Arc<DeltaQExpr>,
    ),
    Gossip {
        #[serde(with = "delta_q_serde")]
        send: Arc<DeltaQExpr>,
        #[serde(with = "delta_q_serde")]
        receive: Arc<DeltaQExpr>,
        size: f32,
        branching: f32,
        cluster_coeff: f32,
        disjoint_names: BTreeSet<Name>,
    },
}

mod delta_q_serde {
    use super::DeltaQExpr;
    use serde::{Deserialize, Serialize};
    use std::sync::Arc;

    pub(super) fn serialize<S>(this: &Arc<DeltaQExpr>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        (**this).serialize(serializer)
    }

    pub(super) fn deserialize<'de, D>(deserializer: D) -> Result<Arc<DeltaQExpr>, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let delta_q = DeltaQExpr::deserialize(deserializer)?;
        Ok(Arc::new(delta_q))
    }
}

impl Display for DeltaQ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        DeltaQ::display(&self.expr, f, false)
    }
}

impl Display for DeltaQExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        DeltaQ::display(&Arc::new(self.clone()), f, false)
    }
}

impl FromStr for DeltaQExpr {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        crate::parser::parse(s)
    }
}

impl FromStr for DeltaQ {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(DeltaQ::from(DeltaQExpr::from_str(s)?))
    }
}

impl From<DeltaQExpr> for DeltaQ {
    fn from(expr: DeltaQExpr) -> Self {
        DeltaQ {
            expr: Arc::new(expr),
            expanded: OnceCell::new(),
        }
    }
}

impl From<Arc<DeltaQExpr>> for DeltaQ {
    fn from(expr: Arc<DeltaQExpr>) -> Self {
        DeltaQ {
            expr,
            expanded: OnceCell::new(),
        }
    }
}

// dropping is stack recursive, so vulnerable to stack overflow
// hence we carefully trampoline dropping it in chunks
impl Drop for DeltaQExpr {
    fn drop(&mut self) {
        thread_local! {
            static DROP_STACK: RefCell<Vec<Arc<DeltaQExpr>>> = RefCell::new(Vec::new());
            static DEPTH: Cell<usize> = Cell::new(0);
            static DROP: Cell<bool> = Cell::new(false);
        }

        if DROP.get() {
            // just remove the custom drop logic exactly once; the contained data need to be dropped normally again
            DROP.set(false);
            return;
        }

        let depth = DEPTH.get();
        DEPTH.set(depth + 1);

        // replace such that the meaty part can actually be dropped before incrementing DEPTH again
        let expr = std::mem::replace(self, DeltaQExpr::BlackBox);
        match &expr {
            DeltaQExpr::BlackBox | DeltaQExpr::Name(..) | DeltaQExpr::Outcome(..) => {}
            DeltaQExpr::Seq(l, _, r) => {
                save(depth, l);
                save(depth, r);
            }
            DeltaQExpr::Choice(l, _, r, _) => {
                save(depth, l);
                save(depth, r);
            }
            DeltaQExpr::ForAll(l, r) => {
                save(depth, l);
                save(depth, r);
            }
            DeltaQExpr::ForSome(l, r) => {
                save(depth, l);
                save(depth, r);
            }
            DeltaQExpr::Gossip { send, receive, .. } => {
                save(depth, send);
                save(depth, receive);
            }
        };
        // switch off special handling for this particular DeltaQExpr
        DROP.set(true);
        drop(expr);

        if depth == 1 {
            while let Some(expr) = DROP_STACK.with(|stack| stack.borrow_mut().pop()) {
                std::mem::drop(expr);
            }
        }
        DEPTH.set(depth);

        fn save(depth: usize, expr: &Arc<DeltaQExpr>) {
            if depth > 100 {
                // retain one more refcount so that it will only be dropped in the `while` loop above
                DROP_STACK.with(|stack| stack.borrow_mut().push(expr.clone()));
            }
        }
    }
}

impl DeltaQ {
    pub fn top() -> DeltaQ {
        static TOP: OnceLock<Arc<DeltaQExpr>> = OnceLock::new();

        let expr = TOP
            .get_or_init(|| Arc::new(DeltaQExpr::Outcome(Outcome::top())))
            .clone();
        let expanded = OnceCell::new();
        expanded.set(Ok(expr.clone())).unwrap();
        DeltaQ { expr, expanded }
    }

    pub fn expr(&self) -> &DeltaQExpr {
        &self.expr
    }

    pub fn arc(&self) -> Arc<DeltaQExpr> {
        self.expr.clone()
    }

    /// Create a new DeltaQ from a name, referencing a variable.
    pub fn name(name: &str) -> DeltaQ {
        DeltaQ {
            expr: Arc::new(DeltaQExpr::Name(name.into(), None)),
            expanded: OnceCell::new(),
        }
    }

    pub fn name_rec(name: &str, rec: Option<usize>) -> DeltaQ {
        DeltaQ {
            expr: Arc::new(DeltaQExpr::Name(name.into(), rec)),
            expanded: OnceCell::new(),
        }
    }

    /// Create a new DeltaQ from a CDF.
    pub fn cdf(cdf: CDF) -> DeltaQ {
        DeltaQ {
            expr: Arc::new(DeltaQExpr::Outcome(Outcome::new(cdf))),
            expanded: OnceCell::new(),
        }
    }

    /// Create a new DeltaQ from the convolution of two DeltaQs.
    pub fn seq(first: DeltaQ, load: LoadUpdate, second: DeltaQ) -> DeltaQ {
        DeltaQ {
            expr: Arc::new(DeltaQExpr::Seq(first.expr, load, second.expr)),
            expanded: OnceCell::new(),
        }
    }

    /// Create a new DeltaQ from a choice between two DeltaQs.
    pub fn choice(first: DeltaQ, first_weight: f32, second: DeltaQ, second_weight: f32) -> DeltaQ {
        DeltaQ {
            expr: Arc::new(DeltaQExpr::Choice(
                first.expr,
                first_weight,
                second.expr,
                second_weight,
            )),
            expanded: OnceCell::new(),
        }
    }

    /// Create a new DeltaQ from a universal quantification over two DeltaQs.
    pub fn for_all(first: DeltaQ, second: DeltaQ) -> DeltaQ {
        DeltaQ {
            expr: Arc::new(DeltaQExpr::ForAll(first.expr, second.expr)),
            expanded: OnceCell::new(),
        }
    }

    /// Create a new DeltaQ from an existential quantification over two DeltaQs.
    pub fn for_some(first: DeltaQ, second: DeltaQ) -> DeltaQ {
        DeltaQ {
            expr: Arc::new(DeltaQExpr::ForSome(first.expr, second.expr)),
            expanded: OnceCell::new(),
        }
    }

    fn display(this: &Arc<DeltaQExpr>, f: &mut fmt::Formatter<'_>, parens: bool) -> fmt::Result {
        match &**this {
            DeltaQExpr::BlackBox => {
                write!(f, "BB")
            }
            DeltaQExpr::Name(name, rec) => {
                if let Some(rec) = rec {
                    write!(f, "{}^{}", name, rec)
                } else {
                    write!(f, "{}", name)
                }
            }
            DeltaQExpr::Outcome(outcome) => {
                write!(f, "{}", outcome)
            }
            DeltaQExpr::Seq(first, load, second) => {
                if parens {
                    write!(f, "(")?;
                }
                DeltaQ::display(first, f, true)?;
                write!(f, " ->-{load} ")?;
                DeltaQ::display(second, f, !matches!(**second, DeltaQExpr::Seq { .. }))?;
                if parens {
                    write!(f, ")")?;
                }
                Ok(())
            }
            DeltaQExpr::Choice(first, first_weight, second, second_weight) => {
                if parens {
                    write!(f, "(")?;
                }
                DeltaQ::display(first, f, !matches!(**first, DeltaQExpr::Seq { .. }))?;
                write!(f, " {}<>{} ", first_weight, second_weight)?;
                DeltaQ::display(
                    second,
                    f,
                    !matches!(**second, DeltaQExpr::Seq { .. } | DeltaQExpr::Choice { .. }),
                )?;
                if parens {
                    write!(f, ")")?;
                }
                Ok(())
            }
            DeltaQExpr::ForAll(first, second) => {
                write!(f, "∀(")?;
                DeltaQ::display(first, f, true)?;
                write!(f, " | ")?;
                DeltaQ::display(second, f, false)?;
                write!(f, ")")
            }
            DeltaQExpr::ForSome(first, second) => {
                write!(f, "∃(")?;
                DeltaQ::display(first, f, true)?;
                write!(f, " | ")?;
                DeltaQ::display(second, f, false)?;
                write!(f, ")")
            }
            DeltaQExpr::Gossip {
                send,
                receive,
                size,
                branching,
                cluster_coeff,
                disjoint_names,
            } => {
                write!(f, "gossip(")?;
                DeltaQ::display(send, f, true)?;
                write!(f, ", ")?;
                DeltaQ::display(receive, f, true)?;
                write!(f, ", {}, {}, {}, [", size, branching, cluster_coeff)?;
                for (idx, name) in disjoint_names.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", name)?;
                }
                write!(f, "])")
            }
        }
    }

    fn expanded(&self) -> Result<&DeltaQExpr, DeltaQError> {
        self.expanded
            .get_or_init(|| self.expand())
            .as_deref()
            .map_err(|e| e.clone())
    }

    fn expand(&self) -> Result<Arc<DeltaQExpr>, DeltaQError> {
        #[derive(Debug)]
        enum Op<'a> {
            Expand(&'a Arc<DeltaQExpr>),
            AssembleSeq(&'a Arc<DeltaQExpr>, LoadUpdate),
            AssembleChoice(&'a Arc<DeltaQExpr>, f32, f32),
            AssembleForAll(&'a Arc<DeltaQExpr>),
            AssembleForSome(&'a Arc<DeltaQExpr>),
            ExpandGossip(f32, f32, f32, BTreeSet<Name>),
        }

        let mut op_stack = Vec::new();
        let mut res_stack = Vec::new();

        op_stack.push(Op::Expand(&self.expr));

        while let Some(op) = op_stack.pop() {
            match op {
                Op::Expand(delta_q) => match &**delta_q {
                    DeltaQExpr::BlackBox | DeltaQExpr::Name(..) | DeltaQExpr::Outcome(_) => {
                        res_stack.push(delta_q.clone());
                    }
                    DeltaQExpr::Seq(first, load, second) => {
                        op_stack.push(Op::AssembleSeq(delta_q, load.clone()));
                        op_stack.push(Op::Expand(second));
                        op_stack.push(Op::Expand(first));
                    }
                    DeltaQExpr::Choice(first, w1, second, w2) => {
                        op_stack.push(Op::AssembleChoice(delta_q, *w1, *w2));
                        op_stack.push(Op::Expand(second));
                        op_stack.push(Op::Expand(first));
                    }
                    DeltaQExpr::ForAll(first, second) => {
                        op_stack.push(Op::AssembleForAll(delta_q));
                        op_stack.push(Op::Expand(second));
                        op_stack.push(Op::Expand(first));
                    }
                    DeltaQExpr::ForSome(first, second) => {
                        op_stack.push(Op::AssembleForSome(delta_q));
                        op_stack.push(Op::Expand(second));
                        op_stack.push(Op::Expand(first));
                    }
                    DeltaQExpr::Gossip {
                        send,
                        receive,
                        size,
                        branching,
                        cluster_coeff,
                        disjoint_names,
                    } => {
                        op_stack.push(Op::ExpandGossip(
                            *size,
                            *branching,
                            *cluster_coeff,
                            disjoint_names.clone(),
                        ));
                        op_stack.push(Op::Expand(receive));
                        op_stack.push(Op::Expand(send));
                    }
                },
                Op::AssembleSeq(delta_q, load) => {
                    let second = res_stack.pop().unwrap();
                    let first = res_stack.pop().unwrap();
                    let expanded = DeltaQExpr::Seq(first, load, second);
                    if expanded == **delta_q {
                        res_stack.push(delta_q.clone());
                    } else {
                        res_stack.push(Arc::new(expanded));
                    }
                }
                Op::AssembleChoice(delta_q, w1, w2) => {
                    let second = res_stack.pop().unwrap();
                    let first = res_stack.pop().unwrap();
                    let expanded = DeltaQExpr::Choice(first, w1, second, w2);
                    if expanded == **delta_q {
                        res_stack.push(delta_q.clone());
                    } else {
                        res_stack.push(Arc::new(expanded));
                    }
                }
                Op::AssembleForAll(delta_q) => {
                    let second = res_stack.pop().unwrap();
                    let first = res_stack.pop().unwrap();
                    let expanded = DeltaQExpr::ForAll(first, second);
                    if expanded == **delta_q {
                        res_stack.push(delta_q.clone());
                    } else {
                        res_stack.push(Arc::new(expanded));
                    }
                }
                Op::AssembleForSome(delta_q) => {
                    let second = res_stack.pop().unwrap();
                    let first = res_stack.pop().unwrap();
                    let expanded = DeltaQExpr::ForSome(first, second);
                    if expanded == **delta_q {
                        res_stack.push(delta_q.clone());
                    } else {
                        res_stack.push(Arc::new(expanded));
                    }
                }
                Op::ExpandGossip(size, branching, cluster_coeff, disjoint_names) => {
                    let receive = res_stack.pop().unwrap();
                    let send = res_stack.pop().unwrap();
                    let expanded = expand_gossip(
                        &send,
                        &receive,
                        size,
                        branching,
                        cluster_coeff,
                        &disjoint_names,
                    )?;
                    res_stack.push(expanded.expr);
                }
            }
            if std::mem::size_of_val(&op_stack[..]) > 1_000_000 {
                return Err(DeltaQError::TooManySteps);
            }
        }

        assert_eq!(res_stack.len(), 1);
        Ok(res_stack.pop().unwrap())
    }

    pub fn eval(
        &self,
        ctx: &PersistentContext,
        ephemeral: &mut EphemeralContext,
    ) -> Result<Outcome, DeltaQError> {
        // evaluation is done using a stack machine with memory on heap in order to avoid stack overflows
        //
        // The operation stack stores the continuation of a computation frame while the operand stack holds results.

        #[derive(Debug)]
        enum Op<'a> {
            /// Evaluate a DeltaQ with the given load factor and push the result on the result stack
            Eval(&'a DeltaQExpr),
            /// construct a sequence from the top two results on the result stack
            Seq {
                load_factor: f32,
                disjoint_names: BTreeSet<Name>,
            },
            /// construct a choice from the top two results on the result stack
            Choice(f32, f32),
            /// construct a forall from the top two results on the result stack
            ForAll,
            /// construct a forsome from the top two results on the result stack
            ForSome,
            /// end recursion for a name
            EndRec(&'a Name),
            /// increment recursion allowance
            IncAllowance(&'a Name),
            /// cache an outcome
            Cache(&'a Name),
        }

        let mut op_stack = Vec::new();
        let mut res_stack = Vec::<Outcome>::new();

        // Start with the initial DeltaQ
        op_stack.push(Op::Eval(self.expanded()?));

        while let Some(op) = op_stack.pop() {
            match op {
                Op::Eval(dq) => {
                    match dq {
                        DeltaQExpr::BlackBox => return Err(DeltaQError::BlackBox),
                        DeltaQExpr::Name(n, r) => {
                            // recursion is only allowed if not yet recursing on this name or there is an existing allowance
                            // which means that a new allowance leads to error if there is an existing one (this would permit
                            // infinite recursion)
                            //
                            // None means not recursing on this name
                            // Some(None) means recursing on this name without allowance
                            // Some(Some(n)) means recursing on this name with n as the remaining allowance
                            if let Some(r) = r {
                                if ephemeral.rec.contains_key(n) {
                                    return Err(DeltaQError::RecursionError(n.to_owned()));
                                }
                                if *r == 0 {
                                    res_stack.push(Outcome::top());
                                    continue;
                                }
                                // subtract the allowance needed for running the evaluation below
                                ephemeral.rec.insert(n.to_owned(), Some(*r - 1));
                                op_stack.push(Op::EndRec(n));
                            } else {
                                match ephemeral.rec.get_mut(n) {
                                    Some(Some(rec)) => {
                                        // recursing with prior allowance
                                        if *rec == 0 {
                                            res_stack.push(Outcome::top());
                                            continue;
                                        } else {
                                            *rec -= 1;
                                            op_stack.push(Op::IncAllowance(n));
                                        }
                                    }
                                    Some(None) => {
                                        // recursing without allowance
                                        return Err(DeltaQError::RecursionError(n.to_owned()));
                                    }
                                    None => {
                                        // evaluating without allowance => prohibit further recursion
                                        ephemeral.rec.insert(n.to_owned(), None);
                                        op_stack.push(Op::EndRec(n));
                                    }
                                }
                            }

                            // Check cache
                            let use_cache = matches!(ephemeral.rec.get(n), Some(None));
                            if use_cache {
                                if let Some(cached_outcome) = ephemeral.cache.get(n) {
                                    res_stack.push(cached_outcome.clone());
                                    continue;
                                }
                            }

                            // Proceed with evaluation
                            let Some((dq, _constraint)) = ctx.ctx.get(n) else {
                                return Err(DeltaQError::NameError(n.to_owned()));
                            };
                            if use_cache {
                                op_stack.push(Op::Cache(n));
                            }
                            op_stack.push(Op::Eval(dq.expanded()?));
                        }
                        DeltaQExpr::Outcome(outcome) => {
                            res_stack.push(outcome.clone());
                        }
                        DeltaQExpr::Seq(first, load, second) => {
                            op_stack.push(Op::Seq {
                                load_factor: load.factor,
                                disjoint_names: load.disjoint_names.clone(),
                            });
                            // evaluate second after first
                            op_stack.push(Op::Eval(second));
                            op_stack.push(Op::Eval(first));
                        }
                        DeltaQExpr::Choice(first, w1, second, w2) => {
                            op_stack.push(Op::Choice(*w1, *w2));
                            op_stack.push(Op::Eval(second));
                            op_stack.push(Op::Eval(first));
                        }
                        DeltaQExpr::ForAll(first, second) => {
                            op_stack.push(Op::ForAll);
                            op_stack.push(Op::Eval(second));
                            op_stack.push(Op::Eval(first));
                        }
                        DeltaQExpr::ForSome(first, second) => {
                            op_stack.push(Op::ForSome);
                            op_stack.push(Op::Eval(second));
                            op_stack.push(Op::Eval(first));
                        }
                        DeltaQExpr::Gossip { .. } => panic!("gossip not expanded"),
                    }
                }
                Op::Seq {
                    load_factor,
                    disjoint_names,
                } => {
                    let second = res_stack
                        .pop()
                        .unwrap()
                        .apply_load_factor(load_factor, ctx)?;
                    let first = res_stack.pop().unwrap();
                    res_stack.push(first.seq(&second, ctx, disjoint_names));
                }
                Op::Choice(w1, w2) => {
                    let second = res_stack.pop().unwrap();
                    let first = res_stack.pop().unwrap();
                    res_stack.push(first.choice(w1 / (w1 + w2), &second, ctx)?);
                }
                Op::ForAll => {
                    let second = res_stack.pop().unwrap();
                    let first = res_stack.pop().unwrap();
                    res_stack.push(first.for_all(&second, ctx));
                }
                Op::ForSome => {
                    let second = res_stack.pop().unwrap();
                    let first = res_stack.pop().unwrap();
                    res_stack.push(first.for_some(&second, ctx));
                }
                Op::EndRec(n) => {
                    ephemeral.rec.remove(n).unwrap();
                }
                Op::IncAllowance(n) => {
                    if let Some(Some(rec)) = ephemeral.rec.get_mut(n) {
                        *rec += 1;
                    }
                }
                Op::Cache(n) => {
                    ephemeral
                        .cache
                        .insert(n.clone(), res_stack.last().unwrap().clone());
                }
            }
            if std::mem::size_of_val(&op_stack[..]) > 1_000_000 {
                return Err(DeltaQError::TooManySteps);
            }
        }

        assert!(res_stack.len() == 1);
        Ok(res_stack.pop().unwrap())
    }
}

// assume that gossiping to a node that already has been reached is free
pub fn expand_gossip(
    send: &DeltaQExpr,
    receive: &DeltaQExpr,
    size: f32,
    branching: f32,
    cluster_coeff: f32,
    disjoint_names: &BTreeSet<Name>,
) -> Result<DeltaQ, DeltaQError> {
    if size <= 1.0 {
        return Ok(DeltaQ::top());
    }
    let cluster_branch = branching * (1.0 - cluster_coeff);

    let mut remaining = size - 1.0;
    let mut steps = vec![];
    let mut senders = 1.0f32;

    while remaining > 1.0 {
        let prev = remaining;
        let eff_branch = if steps.is_empty() {
            branching
        } else {
            cluster_branch
        };
        // go through senders in some arbitrary order, but do it one by one to calculate the overlap between their targets
        // correctly even when approaching gossip completion; this model assumes that the targets are naturally picked
        // from the remaining set of nodes, which is of course incorrect--however, the resulting distribution somehow
        // matches other studies of the Cardano network
        for _sender in 0..senders.ceil() as usize {
            let new_prob = remaining / prev;
            let targets = eff_branch * new_prob;
            remaining -= targets;
            if remaining < 0.0 {
                remaining = 0.0;
                break;
            }
        }
        // new nodes in this round are the senders in the next round
        senders = prev - remaining;
        steps.push((senders, remaining));
        if steps.len() > 10_000 {
            return Err(DeltaQError::TooManySteps);
        }
    }

    let mut ret = Arc::new(DeltaQExpr::BlackBox);
    for (idx, (senders, remaining)) in steps.into_iter().rev().enumerate() {
        #[cfg(target_arch = "wasm32")]
        web_sys::console::log_1(
            &format!("senders: {senders}, remaining: {remaining}, idx: {idx}").into(),
        );
        if remaining > 1.0 {
            ret = Arc::new(DeltaQExpr::Seq(
                Arc::new(DeltaQExpr::Seq(
                    Arc::new(DeltaQExpr::Outcome(Outcome::top())),
                    LoadUpdate::new(senders / (senders + remaining)),
                    Arc::new(DeltaQExpr::Seq(
                        Arc::new(receive.clone()),
                        if idx == 1 {
                            LoadUpdate::new(remaining / (senders * cluster_branch))
                        } else {
                            LoadUpdate::default()
                        },
                        Arc::new(send.clone()),
                    )),
                )),
                LoadUpdate {
                    factor: 1.0,
                    disjoint_names: disjoint_names.clone(),
                },
                Arc::new(DeltaQExpr::Choice(
                    Arc::new(DeltaQExpr::Outcome(Outcome::top())),
                    senders,
                    ret,
                    remaining,
                )),
            ));
        } else {
            ret = Arc::new(receive.clone());
        }
    }

    Ok(DeltaQExpr::Seq(
        Arc::new(DeltaQExpr::Seq(
            Arc::new(DeltaQExpr::Outcome(Outcome::top())),
            LoadUpdate::new(1.0 / size),
            Arc::new(send.clone()),
        )),
        LoadUpdate {
            factor: 1.0,
            disjoint_names: disjoint_names.clone(),
        },
        Arc::new(DeltaQExpr::Choice(DeltaQ::top().expr, 1.0, ret, size - 1.0)),
    )
    .into())
}

// Define the new EphemeralContext struct
pub struct EphemeralContext {
    pub rec: BTreeMap<Name, Option<usize>>,
    pub cache: BTreeMap<Name, Outcome>,
}

impl Default for EphemeralContext {
    fn default() -> Self {
        Self {
            rec: Default::default(),
            cache: Default::default(),
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
        let cdf = CDF::new(&[(1.0, 0.2), (2.0, 0.9)]).unwrap();
        let dq = DeltaQ::cdf(cdf.clone());
        assert_eq!(dq.to_string(), "CDF[(1, 0.2), (2, 0.9)]");
        assert_eq!(dq, "CDF[(1, 0.2), (2, 0.9)]".parse().unwrap());
    }

    #[test]
    fn test_display_seq() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let seq = DeltaQ::seq(dq1, LoadUpdate::default(), dq2);
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
        assert_eq!(for_all.to_string(), "∀(A | B)");
        assert_eq!(for_all, "∀(A | B)".parse().unwrap());
    }

    #[test]
    fn test_display_for_some() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let for_some = DeltaQ::for_some(dq1, dq2);
        assert_eq!(for_some.to_string(), "∃(A | B)");
        assert_eq!(for_some, "∃(A | B)".parse().unwrap());
    }

    #[test]
    fn test_display_nested_seq() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let dq3 = DeltaQ::name("C");
        let nested_seq = DeltaQ::seq(
            dq1,
            LoadUpdate::default(),
            DeltaQ::seq(dq2, LoadUpdate::default(), dq3),
        );
        assert_eq!(nested_seq.to_string(), "A ->- B ->- C");
        assert_eq!(nested_seq, "A ->- (B ->- C)".parse().unwrap());
        assert_eq!(nested_seq, "A ->- B ->- C".parse().unwrap());
    }

    #[test]
    fn test_display_nested_choice() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let dq3 = DeltaQ::name("C");
        let nested_choice = DeltaQ::choice(dq1, 0.3, DeltaQ::choice(dq2, 0.5, dq3, 0.5), 0.7);
        assert_eq!(nested_choice.to_string(), "A 0.3<>0.7 B 0.5<>0.5 C");
        assert_eq!(nested_choice, "A 0.3<>0.7 (B 0.5<>0.5 C)".parse().unwrap());
        assert_eq!(nested_choice, "A 0.3<>0.7 B 0.5<>0.5 C".parse().unwrap());
    }

    #[test]
    fn test_display_nested_for_all() {
        let dq1 = DeltaQ::name("A");
        let dq2 = DeltaQ::name("B");
        let dq3 = DeltaQ::name("C");
        let dq4 = DeltaQ::name("D");
        let nested_for_all = DeltaQ::for_all(
            DeltaQ::for_all(dq1, dq2),
            DeltaQ::seq(dq3, LoadUpdate::default(), dq4),
        );
        assert_eq!(nested_for_all.to_string(), "∀(∀(A | B) | C ->- D)");
        assert_eq!(nested_for_all, "∀(∀(A | B) | C ->- D)".parse().unwrap());
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
        assert_eq!(nested_for_some.to_string(), "∃(∃(A | B) | C 1<>2 D)");
        assert_eq!(nested_for_some, "∃(∃(A | B) | C 1<>2 D)".parse().unwrap());
    }

    #[test]
    fn test_scenario_from_paper_64k() {
        let ctx = btreemap! {
            "single".to_owned() =>
                DeltaQ::cdf(CDF::new(
                    &[(0.024, 1.0 / 3.0), (0.143, 2.0 / 3.0), (0.531, 1.0)],
                )
                .unwrap()),
            "model2".to_owned() =>
                DeltaQ::choice(
                    DeltaQ::name("single"),
                    1.0,
                    DeltaQ::seq(
                        DeltaQ::name("single"),
                        LoadUpdate::default(),
                        DeltaQ::name("single"),
                    ),
                    100.0,
                ),
            "model3".to_owned() =>
                DeltaQ::choice(
                    DeltaQ::name("single"),
                    1.0,
                    DeltaQ::seq(
                        DeltaQ::name("single"),
                        LoadUpdate::default(),
                        DeltaQ::name("model2"),
                    ),
                    100.0,
                ),
            "model4".to_owned() =>
                DeltaQ::choice(
                    DeltaQ::name("single"),
                    1.0,
                    DeltaQ::seq(
                        DeltaQ::name("single"),
                        LoadUpdate::default(),
                        DeltaQ::name("model3"),
                    ),
                    100.0,
                ),
            "model5".to_owned() =>
                DeltaQ::choice(
                    DeltaQ::name("single"),
                    1.0,
                    DeltaQ::seq(
                        DeltaQ::name("single"),
                        LoadUpdate::default(),
                        DeltaQ::name("model4"),
                    ),
                    100.0,
                ),
        };
        let result = DeltaQ::name("model5")
            .eval(&ctx.into(), &mut EphemeralContext::default())
            .unwrap();
        assert_eq!(result.to_string(), "CDF[(0.024, 0.0033), (0.048, 0.00439), (0.072, 0.00475), (0.096, 0.00487), (0.12, 0.00882), (0.143, 0.01212), (0.167, 0.0143), (0.191, 0.01538), (0.215, 0.01585), (0.239, 0.03563), (0.286, 0.03672), (0.31, 0.03779), (0.334, 0.03851), (0.358, 0.07805), (0.429, 0.07841), (0.453, 0.07889), (0.477, 0.11843), (0.531, 0.12173), (0.555, 0.12391), (0.572, 0.12403), (0.579, 0.12511), (0.596, 0.14488), (0.603, 0.14536), (0.627, 0.16513), (0.674, 0.16731), (0.698, 0.16947), (0.715, 0.17342), (0.722, 0.17484), (0.746, 0.25394), (0.817, 0.25502), (0.841, 0.25644), (0.865, 0.37508), (0.96, 0.37555), (0.984, 0.45465), (1.062, 0.45574), (1.086, 0.45681), (1.103, 0.47659), (1.11, 0.4773), (1.134, 0.51685), (1.205, 0.51792), (1.229, 0.51935), (1.253, 0.63799), (1.348, 0.6387), (1.372, 0.75734), (1.491, 0.79689), (1.593, 0.79725), (1.617, 0.79772), (1.641, 0.83727), (1.736, 0.83774), (1.76, 0.91683), (1.879, 0.95638), (2.124, 0.9565), (2.148, 0.97627), (2.267, 0.99605), (2.655, 1)]");
    }

    #[test]
    fn test_recursive_deltaq() {
        let ctx = btreemap! {
            "recursive".to_owned() =>
                DeltaQ::choice(
                    DeltaQ::name("base"),
                    1.0,
                    DeltaQ::seq(
                        DeltaQ::name("base"),
                        LoadUpdate::default(),
                        DeltaQ::name("recursive"),
                    ),
                    1.0,
                ),
            "base".to_owned() => DeltaQ::cdf(CDF::new(&[(1.0, 0.5), (2.0,1.0)]).unwrap()),
        };
        let result = DeltaQ::name("recursive")
            .eval(&ctx.into(), &mut EphemeralContext::default())
            .unwrap_err();
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
            res.contains("expected 'BB', name, CDF, 'all(', 'some(', 'gossip(', or parentheses"),
            "{}",
            res
        );
    }

    #[test]
    fn parse_outcome() {
        let expected = Outcome::new_with_load(
            CDF::new(&[(1.0, 0.1), (2.0, 0.3)]).unwrap(),
            btreemap! {
                "metric".into() => StepFunction::new(&[(0.0, 12.0), (1.5, 0.0)]).unwrap(),
            },
        );
        assert_eq!(
            DeltaQExpr::Outcome(expected),
            "CDF[(1, 0.1), (2, 0.3)] WITH metric[(0, 12), (1.5, 0)]"
                .parse::<DeltaQExpr>()
                .unwrap()
        );
    }

    #[test]
    fn parse_load_update() {
        let res = "BB ->-*3 BB".parse::<DeltaQExpr>().unwrap();
        assert_eq!(
            res,
            DeltaQExpr::Seq(
                Arc::new(DeltaQExpr::BlackBox),
                LoadUpdate::new(3.0),
                Arc::new(DeltaQExpr::BlackBox)
            )
        );
        assert_eq!(res.to_string(), "BB ->-×3 BB");
    }

    #[test]
    fn test_recursion() {
        let mut ctx = PersistentContext::default();
        let mut ephemeral = EphemeralContext::default();

        ctx.put("f".to_owned(), "CDF[(1,1)] ->- f ->- f".parse().unwrap());
        let res = DeltaQ::name_rec("f", Some(3))
            .eval(&ctx, &mut ephemeral)
            .unwrap();
        assert_eq!(
            DeltaQExpr::Outcome(res),
            outcome.parse("CDF[(7,1)]").unwrap()
        );
        let res = DeltaQ::name_rec("f", Some(0))
            .eval(&ctx, &mut ephemeral)
            .unwrap();
        assert_eq!(
            DeltaQExpr::Outcome(res),
            outcome.parse("CDF[(0,1)]").unwrap()
        );

        ctx.put("f".to_owned(), "CDF[(1,1)] ->- f".parse().unwrap());
        for i in 0..10 {
            let res = DeltaQ::name_rec("f", Some(i))
                .eval(&ctx, &mut ephemeral)
                .unwrap();
            assert_eq!(
                DeltaQExpr::Outcome(res),
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
        let res = DeltaQ::name_rec("out", Some(1))
            .eval(&ctx, &mut ephemeral)
            .unwrap();
        assert_eq!(
            res.cdf,
            CDF::new(&[
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
        assert_eq!(ctx.get("diffuse").unwrap().to_string(), "hop 0.6<>99.4 hop ->- hop 8.58<>90.82 (hop ->- hop) ->- hop 65.86<>24.96 ((hop ->- hop) ->- hop) ->- hop");

        const DEST: &'static str = "\
            diffuse := hop 0.6<>99.4 hop ->- hop 8.58<>90.82 (hop ->- hop) ->- hop 65.86<>24.96 ((hop ->- hop) ->- hop) ->- hop\n\
            diffuseEB := hopEB 0.6<>99.4 hopEB ->- hopEB 8.58<>90.82 (hopEB ->- hopEB) ->- hopEB 65.86<>24.96 ((hopEB ->- hopEB) ->- hopEB) ->- hopEB\n\
            far := CDF[(0.268, 1)]\n\
            farL := CDF[(0.531, 1)]\n\
            farXL := CDF[(1.598, 1)]\n\
            hop := ((near ->- near) ->- near) ->- nearXL 1<>2 ((mid ->- mid) ->- mid) ->- midXL 1<>1 ((far ->- far) ->- far) ->- farXL\n\
            hopEB := ((near ->- near) ->- near) ->- nearL 1<>2 ((mid ->- mid) ->- mid) ->- midL 1<>1 ((far ->- far) ->- far) ->- farL\n\
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
        let outcome = Outcome::new_with_load(
            CDF::new(&[(1.5, 0.1)]).unwrap(),
            btreemap! {
                "net".into() => StepFunction::new(&[(0.0, 12.0), (1.0, 0.0)]).unwrap(),
            },
        );
        let dq = DeltaQ::from(DeltaQExpr::Seq(
            Arc::new(DeltaQExpr::Outcome(outcome.clone())),
            LoadUpdate::new(0.5),
            Arc::new(DeltaQExpr::Outcome(outcome)),
        ));
        assert_eq!(dq.to_string(), "CDF[(1.5, 0.1)] WITH net[(0, 12), (1, 0)] ->-×0.5 CDF[(1.5, 0.1)] WITH net[(0, 12), (1, 0)]");
        let ctx = PersistentContext::default();
        let mut ephemeral = EphemeralContext::default();
        let res = dq.eval(&ctx, &mut ephemeral).unwrap();
        let expected = Outcome::new(CDF::new(&[(3.0, 0.010000001)]).unwrap()).with_load(
            "net".into(),
            StepFunction::try_from(&[
                (0.0, CDF::from_step_at(12.0)),
                (1.0, CDF::from_step_at(0.0)),
                (1.5, CDF::new(&[(0.0, 0.05), (12.0, 0.1)]).unwrap()),
                (2.5, CDF::new(&[(0.0, 0.1)]).unwrap()),
            ])
            .unwrap(),
        );
        assert_eq!(res, expected);
    }

    #[test]
    fn distributive_choice() {
        let ctx = eval_ctx("\
            a := CDF[(1, 0.4), (2, 1)] WITH common[(0.1, 3), (0.8, 0)] WITH a[(0,1), (1,0)] WITH ab[(0, 12), (1,0)]
            b := CDF[(2, 0.5), (3, 1)] WITH common[(0.2, 0.1), (1.2, 0.2), (1.5, 0)] WITH b[(0,1), (2,0)] WITH ab[(0, 7), (2,0)]
            c := CDF[(3, 0.6), (4, 1)] WITH common[(2.4, 100), (2.5, 0)] WITH c[(0,1), (3,0)]

            e1 := a ->- b 1<>2 a ->- c
            e2 := a ->- (b 1<>2 c)
            ").unwrap();
        let e1 = DeltaQ::name("e1")
            .eval(&ctx, &mut EphemeralContext::default())
            .unwrap();
        let e2 = DeltaQ::name("e2")
            .eval(&ctx, &mut EphemeralContext::default())
            .unwrap();
        assert!(e1.similar(&e2), "{e1}\ndoes not match\n{e2}");

        let ctx = eval_ctx("\
            a := CDF[(1, 0.4), (2, 1)] WITH common[(0.1, 3), (0.8, 0)] WITH a[(0,1), (1,0)] WITH ab[(0, 12), (1,0)]
            b := CDF[(2, 0.5), (3, 1)] WITH common[(0.2, 0.1), (1.2, 0.2), (1.5, 0)] WITH b[(0,1), (2,0)] WITH ab[(0, 7), (2,0)]
            c := CDF[(3, 0.6), (4, 1)] WITH common[(2.4, 100), (2.5, 0)] WITH c[(0,1), (3,0)]

            e1 := a ->-×0.3 b 1<>2 a ->-×0.3 c
            e2 := a ->-×0.3 (b 1<>2 c)
            ").unwrap();
        let e1 = DeltaQ::name("e1")
            .eval(&ctx, &mut EphemeralContext::default())
            .unwrap();
        let e2 = DeltaQ::name("e2")
            .eval(&ctx, &mut EphemeralContext::default())
            .unwrap();
        assert!(e1.similar(&e2), "{e1}\ndoes not match\n{e2}");
    }

    #[test]
    fn test_load_factor() {
        let ctx = eval_ctx("\
            a := CDF[(1, 0.4), (2, 1)] WITH common[(0.1, 3), (0.8, 0)] WITH a[(0,1), (1,0)] WITH ab[(0, 12), (1,0)]
            b := CDF[(2, 0.5), (3, 1)] WITH common[(0.2, 0.1), (1.2, 0.2), (1.5, 0)] WITH b[(0,1), (2,0)] WITH ab[(0, 7), (2,0)]
            
            e1 := a ->-×0.8 a ->-×0.7 b
            e2 := CDF[(1, 0.4), (2, 1)] WITH common[(0.1, 3), (0.8, 0)] WITH a[(0,1), (1,0)] WITH ab[(0, 12), (1,0)]
                ->-×0.8 CDF[(1, 0.4), (2, 1)] WITH common[(0.1, 3), (0.8, 0)] WITH a[(0,1), (1,0)] WITH ab[(0, 12), (1,0)]
                ->-×0.7 CDF[(2, 0.5), (3, 1)] WITH common[(0.2, 0.1), (1.2, 0.2), (1.5, 0)] WITH b[(0,1), (2,0)] WITH ab[(0, 7), (2,0)]
            ").unwrap();
        let e1 = DeltaQ::name("e1")
            .eval(&ctx, &mut EphemeralContext::default())
            .unwrap();
        let e2 = DeltaQ::name("e2")
            .eval(&ctx, &mut EphemeralContext::default())
            .unwrap();
        assert!(e1.similar(&e2), "{e1}\ndoes not match\n{e2}");
        assert_eq!(e1.to_string(), "\
            CDF[(4, 0.08), (5, 0.4), (6, 0.82), (7, 1)] \
            WITH a[(0, 1), (1, CDF[(0, 0.68), (1, 1)]), (2, CDF[(0, 0.52), (1, 1)]), (3, 0)] \
            WITH ab[(0, 12), (1, CDF[(0, 0.68), (12, 1)]), (2, CDF[(0, 0.4304), (7, 0.52), (12, 1)]), (3, CDF[(0, 0.6416), (7, 1)]), (4, CDF[(0, 0.5296), (7, 1)]), (5, CDF[(0, 0.7984), (7, 1)]), (6, 0)] \
            WITH b[(2, CDF[(0, 0.9104), (1, 1)]), (3, CDF[(0, 0.6416), (1, 1)]), (4, CDF[(0, 0.5296), (1, 1)]), (5, CDF[(0, 0.7984), (1, 1)]), (6, 0)] \
            WITH common[(0.1, 3), (0.8, 0), (1.1, CDF[(0, 0.68), (3, 1)]), (1.8, 0), (2.1, CDF[(0, 0.52), (3, 1)]), (2.2, CDF[(0, 0.4304), (0.1, 0.52), (3, 1)]), \
            (2.8, CDF[(0, 0.9104), (0.1, 1)]), (3.2, CDF[(0, 0.6416), (0.1, 0.9104), (0.2, 1)]), (3.5, CDF[(0, 0.7312), (0.1, 1)]), \
            (4.2, CDF[(0, 0.5296), (0.1, 0.7312), (0.2, 1)]), (4.5, CDF[(0, 0.7984), (0.1, 1)]), (5.2, CDF[(0, 0.7984), (0.2, 1)]), (5.5, 0)]");
    }

    #[test]
    fn test_gossip() {
        let ctx: PersistentContext = "diffuse := gossip(hop, CDF[(0, 1)], 3000, 15, 0.1, [])
            hop := CDF[(1, 1)] WITH net[(0, 1), (1, 0)]"
            .parse()
            .unwrap();
        let diffuse = ctx.eval("diffuse").unwrap();
        assert_eq!(diffuse.to_string(), "CDF[(1, 0.00033), (2, 0.00533), (3, 0.07074), (4, 1)] \
            WITH net[(0, CDF[(0, 0.99967), (1, 1)]), (1, CDF[(0, 0.995), (1, 1)]), (2, CDF[(0, 0.9346), (1, 1)]), (3, CDF[(0, 0.97355), (1, 1)]), (4, 0)]");

        // this test made sense when the gossip impl was broken; need to figure out whether to keep it
        // let ctx: PersistentContext = "diffuse := gossip(hop, 3000, 15, 0.95)
        //         hop := CDF[(1, 1)] WITH net[(0, 1), (1, 0)]"
        //     .parse()
        //     .unwrap();
        // let diffuse = ctx.eval("diffuse").unwrap();
        // assert_eq!(diffuse.cdf.iter().count(), 1000);
        // assert!(
        //     diffuse.cdf.steps().integrate(0.0, 1476.0) > 737.0,
        //     "{}",
        //     diffuse.cdf.steps().integrate(0.0, 1476.0)
        // );
        // assert!(diffuse.cdf.steps().at(1200.0) > 0.95);
    }
}
