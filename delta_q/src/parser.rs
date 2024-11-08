use crate::{
    delta_q::{LoadUpdate, Name},
    DeltaQ, DeltaQExpr, Outcome, PersistentContext, StepFunction, CDF,
};
use std::sync::Arc;
use winnow::{
    combinator::{
        alt, cut_err, delimited, fail, opt, preceded, repeat, separated, separated_pair, seq,
    },
    error::{StrContext, StrContextValue},
    stream::{Accumulate, Stream},
    token::take_while,
    PResult, Parser,
};

pub fn eval_ctx(input: &str) -> Result<PersistentContext, String> {
    repeat(
        0..,
        delimited(
            ws,
            separated_pair(
                (name_bare, opt((ws, ">=", ws, name_bare).map(|x| x.3))),
                (ws, ":=", ws),
                delta_q,
            ),
            ws,
        ),
    )
    .parse(input)
    .map_err(|e| format!("{e}"))
}

impl<'a> Accumulate<((&'a str, Option<&'a str>), DeltaQExpr)> for PersistentContext {
    fn accumulate(&mut self, ((name, constraint), dq): ((&'a str, Option<&'a str>), DeltaQExpr)) {
        self.put(name.to_owned(), DeltaQ::from(dq));
        if let Some(constraint) = constraint {
            self.set_constraint(name, Some(constraint.into()));
        }
    }

    fn initial(_capacity: Option<usize>) -> Self {
        PersistentContext::default()
    }
}

pub fn parse(input: &str) -> Result<DeltaQExpr, String> {
    delta_q.parse(input).map_err(|e| format!("{e}"))
}

fn delta_q(input: &mut &str) -> PResult<DeltaQExpr> {
    // https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
    fn rec(input: &mut &str, min_bp: u8) -> PResult<DeltaQExpr> {
        let mut lhs = atom.parse_next(input)?;

        loop {
            let snap = input.checkpoint();
            let Ok(op) = alt((
                op_seq.map(|mult| Op::Seq { mult }),
                (num, "<>", num).map(|(l, _, r)| Op::Choice(l, r)),
            ))
            .parse_next(input) else {
                break;
            };

            let (lbp, rbp) = op.bp();
            if lbp < min_bp {
                input.reset(&snap);
                break;
            }

            let rhs = rec(input, rbp)?;
            lhs = match op {
                Op::Seq { mult } => {
                    DeltaQExpr::Seq(Arc::new(lhs), LoadUpdate::new(mult), Arc::new(rhs))
                }
                Op::Choice(l, r) => DeltaQExpr::Choice(Arc::new(lhs), l, Arc::new(rhs), r),
            };
        }
        Ok(lhs)
    }
    rec(input, 0)
}

fn op_seq(input: &mut &str) -> PResult<f32> {
    (
        "->-",
        opt(preceded(alt(('*', '×', '⋅')), num)).map(|x| x.unwrap_or(1.0)),
    )
        .map(|x| x.1)
        .parse_next(input)
}

fn atom(input: &mut &str) -> PResult<DeltaQExpr> {
    delimited(
        ws,
        alt((
            blackbox,
            outcome,
            for_all,
            for_some,
            gossip,
            name,
            delimited('(', delta_q, closing_paren),
            fail.context(StrContext::Label("atom"))
                .context(StrContext::Expected(StrContextValue::Description(
                    "'BB', name, CDF, 'all(', 'some(', 'gossip(', or parentheses",
                ))),
        )),
        ws,
    )
    .parse_next(input)
}

fn ws(input: &mut &str) -> PResult<()> {
    let white = take_while(0.., |c: char| c.is_whitespace()).void();
    let comment = ("--", take_while(0.., |c: char| c != '\n'), opt('\n')).void();
    separated::<_, _, (), _, _, _, _>(0.., white, comment)
        .void()
        .parse_next(input)
}

fn blackbox(input: &mut &str) -> PResult<DeltaQExpr> {
    "BB".value(DeltaQExpr::BlackBox).parse_next(input)
}

fn name_bare<'a>(input: &mut &'a str) -> PResult<&'a str> {
    take_while(1.., |c: char| c.is_alphanumeric() || c == '_').parse_next(input)
}

fn name(input: &mut &str) -> PResult<DeltaQExpr> {
    (name_bare, opt(preceded('^', int)))
        .parse_next(input)
        .map(|(name, rec)| DeltaQExpr::Name(name.into(), rec))
}

pub(crate) fn outcome(input: &mut &str) -> PResult<DeltaQExpr> {
    (cdf, repeat::<_, _, Vec<_>, _, _>(0.., preceded(ws, load)))
        .map(|(cdf, loads)| {
            DeltaQExpr::Outcome(Outcome::new_with_load(cdf, loads.into_iter().collect()))
        })
        .parse_next(input)
}

fn cdf(input: &mut &str) -> PResult<CDF> {
    preceded(
        "CDF",
        cut_err(step_function.try_map(|x| CDF::from_step_function(x)))
            .context(StrContext::Label("CDF")),
    )
    .parse_next(input)
}

fn load(input: &mut &str) -> PResult<(Name, StepFunction)> {
    preceded(
        "WITH ",
        cut_err((name_bare.map(|s| Name::from(s)), step_function)),
    )
    .parse_next(input)
}

fn step_function(input: &mut &str) -> PResult<StepFunction> {
    delimited('[', step_function_body, ']').parse_next(input)
}

fn step_function_body(input: &mut &str) -> PResult<StepFunction> {
    cut_err(
        separated::<_, _, Vec<_>, _, _, _, _>(
            0..,
            (ws, '(', ws, num, ws, ',', ws, num, ws, ')').map(|x| (x.3, x.7)),
            (ws, ','),
        )
        .try_map(|steps| StepFunction::new(&steps))
        .context(StrContext::Label("step function")),
    )
    .parse_next(input)
}

fn for_all(input: &mut &str) -> PResult<DeltaQExpr> {
    delimited(
        alt(("all(", "∀(")),
        cut_err(separated_pair(delta_q, "|", delta_q)),
        closing_paren,
    )
    .map(|(left, right)| DeltaQExpr::ForAll(Arc::new(left), Arc::new(right)))
    .parse_next(input)
}

fn for_some(input: &mut &str) -> PResult<DeltaQExpr> {
    delimited(
        alt(("some(", "∃(")),
        cut_err(separated_pair(delta_q, "|", delta_q)),
        closing_paren,
    )
    .map(|(left, right)| DeltaQExpr::ForSome(Arc::new(left), Arc::new(right)))
    .parse_next(input)
}

fn gossip(input: &mut &str) -> PResult<DeltaQExpr> {
    delimited(
        "gossip(",
        cut_err(seq!(delta_q, _: comma, num, _: comma, num, _: comma, num))
            .context(StrContext::Label("gossip specification"))
            .context(StrContext::Expected(StrContextValue::Description(
                "hop, size, branching, cluster coefficient",
            ))),
        closing_paren,
    )
    .map(|(dq, size, branching, cluster_coeff)| DeltaQExpr::Gossip {
        hop: Arc::new(dq),
        size,
        branching,
        cluster_coeff,
    })
    .parse_next(input)
}

fn comma(input: &mut &str) -> PResult<()> {
    cut_err((ws, ',', ws))
        .void()
        .context(StrContext::Label("comma"))
        .parse_next(input)
}

fn num(input: &mut &str) -> PResult<f32> {
    take_while(1.., |c: char| c.is_digit(10) || c == '.')
        .try_map(|num_str: &str| num_str.parse::<f32>())
        .context(StrContext::Label("number"))
        .parse_next(input)
}

fn int(input: &mut &str) -> PResult<usize> {
    take_while(1.., |c: char| c.is_digit(10))
        .try_map(|num_str: &str| num_str.parse::<usize>())
        .context(StrContext::Label("integer"))
        .parse_next(input)
}

fn closing_paren(input: &mut &str) -> PResult<()> {
    cut_err(')')
        .void()
        .context(StrContext::Expected(StrContextValue::Description(
            "closing parenthesis",
        )))
        .parse_next(input)
}

#[derive(Debug, Clone, Copy)]
enum Op {
    Seq { mult: f32 },
    Choice(f32, f32),
}

impl Op {
    fn bp(&self) -> (u8, u8) {
        match self {
            Op::Choice { .. } => (2, 1),
            Op::Seq { .. } => (4, 3),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_empty_cdf() {
        assert_eq!(
            parse("CDF[]"),
            Ok(DeltaQExpr::Outcome(Outcome::new(
                CDF::from_steps(&[]).unwrap()
            )))
        );
    }

    #[test]
    fn parse_errors() {
        assert_eq!(
            parse("CDF[1, 2]").unwrap_err(),
            "CDF[1, 2]\n    ^\ninvalid CDF"
        );
        assert_eq!(
            parse("CDF[(1, 2)]").unwrap_err(),
            "CDF[(1, 2)]\n   ^\ninvalid CDF\nData vector must contain values between 0 and 1"
        );
    }
}
