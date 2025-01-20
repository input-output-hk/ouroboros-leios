use rustc_apfloat::{
    Float, FloatConvert,
    ieee::{Double, IeeeFloat, Quad},
};

pub fn into_quad(x: f64) -> Quad {
    let y: Double = Double::from_bits(x.to_bits() as u128);
    let loses_info: &mut bool = &mut false;
    IeeeFloat::convert(y, loses_info).value
}

fn add(x: Quad, y: Quad) -> Quad {
    (x + y).value
}

fn sub(x: Quad, y: Quad) -> Quad {
    (x - y).value
}

fn mul(x: Quad, y: Quad) -> Quad {
    (x * y).value
}

fn div(x: Quad, y: Quad) -> Quad {
    (x / y).value
}

pub fn ln_1_minus(f: Quad) -> Quad {
    let mut acc: Quad = Quad::ZERO;
    let mut prev: Quad = Quad::from_i128(1).value;
    let mut i: i128 = 1;
    loop {
        let term: Quad = mul(prev, f);
        let acc1: Quad = sub(acc, div(term, Quad::from_i128(i).value));
        if acc == acc1 {
            break acc;
        }
        prev = term;
        acc = acc1;
        i += 1;
    }
}

pub fn leader_check(ln1f: Quad, s: Quad, p: Quad) -> bool {
    let t0: Quad = mul(s, ln1f);
    let mut acc: Quad = Quad::ZERO;
    let mut prev: Quad = Quad::from_i128(1).value;
    let mut i: i128 = 1;
    loop {
        let term: Quad = div(mul(prev, t0), Quad::from_i128(i).value);
        let err: Quad = term.abs();
        let acc1: Quad = sub(acc, term);
        if p < sub(acc1, err) {
            break true;
        } else if p > add(acc1, err) {
            break false;
        }
        prev = term;
        acc = acc1;
        i += 1;
    }
}

pub fn leader_value(ln1f: Quad, s: Quad) -> Quad {
    let x: Quad = mul(ln1f, s);
    let mut acc: Quad = Quad::ZERO;
    let mut prev: Quad = Quad::from_i128(1).value;
    let mut i: i128 = 1;
    loop {
        let term: Quad = div(mul(prev, x), Quad::from_i128(i).value);
        let acc1: Quad = sub(acc, term);
        // FIXME: This could be terminated sooner if we do a careful analysis of errors.
        if acc == acc1 {
            break acc;
        }
        prev = term;
        acc = acc1;
        i += 1;
    }
}

fn exp(x: Quad) -> Quad {
    let mut prev: Quad = Quad::from_i128(1).value;
    let mut acc: Quad = prev;
    let mut i: i128 = 1;
    loop {
        let term: Quad = div(mul(prev, x), Quad::from_i128(i).value);
        let acc1: Quad = add(acc, term);
        // FIXME: This could be terminated sooner if we do a careful analysis of errors.
        if acc == acc1 {
            break acc;
        }
        prev = term;
        acc = acc1;
        i += 1;
    }
}

pub fn voter_check(votes: Quad, s: Quad, p: Quad) -> i128 {
    let x: Quad = mul(votes, s);
    let v: Quad = div(p, exp(mul(Quad::from_i128(-1).value, x)));
    let mut i: i128 = 0;
    let mut prev: Quad = Quad::from_i128(1).value;
    let mut acc: Quad = prev;
    loop {
        if v <= acc || i > 10 {
            break i;
        }
        i += 1;
        let ii: Quad = Quad::from_i128(i).value;
        if ii == votes {
            break i;
        }
        let term: Quad = div(mul(prev, x), ii);
        acc = add(acc, term);
        prev = term;
    }
}
