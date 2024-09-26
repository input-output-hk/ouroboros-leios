use crate::DeltaQ;
use winnow::{
    combinator::{alt, delimited, repeat, separated_pair},
    stream::Stream,
    token::take_while,
    PResult, Parser,
};

pub fn parse(input: &str) -> Result<DeltaQ, String> {
    delta_q
        .parse(input)
        .map_err(|e| format!("ΔQ parse error: {} (at position {})", e.inner(), e.offset()))
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
                Op::Seq => DeltaQ::Seq(Box::new(lhs), Box::new(rhs)),
                Op::Choice(l, r) => DeltaQ::Choice(Box::new(lhs), l, Box::new(rhs), r),
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
            name,
            cdf,
            for_all,
            for_some,
            delimited('(', delta_q, ')'),
        )),
        ws,
    )
    .parse_next(input)
}

fn ws(input: &mut &str) -> PResult<()> {
    take_while(0.., |c: char| c.is_whitespace())
        .void()
        .parse_next(input)
}

fn blackbox(input: &mut &str) -> PResult<DeltaQ> {
    "BB".value(DeltaQ::BlackBox).parse_next(input)
}

fn name(input: &mut &str) -> PResult<DeltaQ> {
    take_while(1.., |c: char| c.is_alphanumeric())
        .parse_next(input)
        .map(|name| DeltaQ::Name(name.to_string()))
}

fn cdf(input: &mut &str) -> PResult<DeltaQ> {
    (
        "CDF[",
        repeat::<_, _, (), _, _>(0.., (ws, '(', ws, num, ws, ',', ws, num, ws, ')')),
        ws,
        "]",
    )
        .take()
        .try_map(|s| s.parse().map(DeltaQ::CDF))
        .parse_next(input)
}

fn for_all(input: &mut &str) -> PResult<DeltaQ> {
    delimited("all(", separated_pair(delta_q, "|", delta_q), ")")
        .map(|(left, right)| DeltaQ::ForAll(Box::new(left), Box::new(right)))
        .parse_next(input)
}

fn for_some(input: &mut &str) -> PResult<DeltaQ> {
    delimited("some(", separated_pair(delta_q, "|", delta_q), ")")
        .map(|(left, right)| DeltaQ::ForSome(Box::new(left), Box::new(right)))
        .parse_next(input)
}

fn num(input: &mut &str) -> PResult<f32> {
    take_while(1.., |c: char| c.is_digit(10) || c == '.')
        .parse_next(input)
        .map(|num_str| num_str.parse::<f32>().unwrap())
}

#[derive(Debug, Clone, Copy)]
enum Op {
    Seq,
    Choice(f32, f32),
}

impl Op {
    fn bp(&self) -> (u8, u8) {
        match self {
            Op::Seq => (1, 2),
            Op::Choice { .. } => (3, 4),
        }
    }
}
