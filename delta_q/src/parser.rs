use crate::{DeltaQ, EvaluationContext};
use std::sync::Arc;
use winnow::{
    combinator::{alt, cut_err, delimited, fail, opt, preceded, repeat, separated, separated_pair},
    error::{StrContext, StrContextValue},
    stream::{Accumulate, Stream},
    token::take_while,
    PResult, Parser,
};

pub fn eval_ctx(input: &str) -> Result<EvaluationContext, String> {
    repeat(
        0..,
        delimited(ws, separated_pair(name_bare, (ws, ":=", ws), delta_q), ws),
    )
    .parse(input)
    .map_err(|e| format!("{e}"))
}

impl<'a> Accumulate<(&'a str, DeltaQ)> for EvaluationContext {
    fn accumulate(&mut self, (name, dq): (&'a str, DeltaQ)) {
        self.put(name.to_owned(), dq);
    }

    fn initial(_capacity: Option<usize>) -> Self {
        EvaluationContext::default()
    }
}

pub fn parse(input: &str) -> Result<DeltaQ, String> {
    delta_q.parse(input).map_err(|e| format!("{e}"))
}

fn delta_q(input: &mut &str) -> PResult<DeltaQ> {
    // https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
    fn rec(input: &mut &str, min_bp: u8) -> PResult<DeltaQ> {
        let mut lhs = atom.parse_next(input)?;

        loop {
            let snap = input.checkpoint();
            let Ok(op) = alt((
                "->-".value(Op::Seq),
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
                Op::Seq => DeltaQ::Seq(Arc::new(lhs), Arc::new(rhs)),
                Op::Choice(l, r) => DeltaQ::Choice(Arc::new(lhs), l, Arc::new(rhs), r),
            };
        }
        Ok(lhs)
    }
    rec(input, 0)
}

fn atom(input: &mut &str) -> PResult<DeltaQ> {
    delimited(
        ws,
        alt((
            blackbox,
            cdf,
            for_all,
            for_some,
            name,
            delimited('(', delta_q, closing_paren),
            fail.context(StrContext::Label("atom"))
                .context(StrContext::Expected(StrContextValue::Description(
                    "'BB', name, CDF, 'all(', 'some(', or a parentheses",
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

fn blackbox(input: &mut &str) -> PResult<DeltaQ> {
    "BB".value(DeltaQ::BlackBox).parse_next(input)
}

fn name_bare<'a>(input: &mut &'a str) -> PResult<&'a str> {
    take_while(1.., |c: char| c.is_alphanumeric()).parse_next(input)
}

fn name(input: &mut &str) -> PResult<DeltaQ> {
    (name_bare, opt(preceded('^', int)))
        .parse_next(input)
        .map(|(name, rec)| DeltaQ::name_rec(name, rec))
}

fn cdf(input: &mut &str) -> PResult<DeltaQ> {
    (
        "CDF[",
        cut_err(
            separated::<_, _, (), _, _, _, _>(
                0..,
                (ws, '(', ws, cut_err((num, ws, ',', ws, num, ws, ')')))
                    .context(StrContext::Label("CDF literal"))
                    .context(StrContext::Expected(StrContextValue::Description(
                        "CDF[(<num>, <num>), ...]",
                    ))),
                (ws, ','),
            )
            .take()
            .try_map(|s: &str| {
                //
                s.parse().map(DeltaQ::CDF)
            }),
        ),
        ws,
        cut_err(
            "]".context(StrContext::Expected(StrContextValue::Description(
                "closing bracket",
            ))),
        ),
    )
        .map(|x| x.1)
        .parse_next(input)
}

fn for_all(input: &mut &str) -> PResult<DeltaQ> {
    delimited(
        "all(",
        cut_err(separated_pair(delta_q, "|", delta_q)),
        closing_paren,
    )
    .map(|(left, right)| DeltaQ::ForAll(Arc::new(left), Arc::new(right)))
    .parse_next(input)
}

fn for_some(input: &mut &str) -> PResult<DeltaQ> {
    delimited(
        "some(",
        cut_err(separated_pair(delta_q, "|", delta_q)),
        closing_paren,
    )
    .map(|(left, right)| DeltaQ::ForSome(Arc::new(left), Arc::new(right)))
    .parse_next(input)
}

fn num(input: &mut &str) -> PResult<f32> {
    take_while(1.., |c: char| c.is_digit(10) || c == '.')
        .try_map(|num_str: &str| num_str.parse::<f32>())
        .parse_next(input)
}

fn int(input: &mut &str) -> PResult<usize> {
    take_while(1.., |c: char| c.is_digit(10))
        .try_map(|num_str: &str| num_str.parse::<usize>())
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
    Seq,
    Choice(f32, f32),
}

impl Op {
    fn bp(&self) -> (u8, u8) {
        match self {
            Op::Choice { .. } => (2, 1),
            Op::Seq => (3, 4),
        }
    }
}
