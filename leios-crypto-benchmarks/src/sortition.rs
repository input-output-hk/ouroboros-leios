
use rustc_apfloat::{ieee::{IeeeFloat,Double,Quad},Float,FloatConvert};

pub fn into_quad(x : f64) -> Quad {
  let y : Double = Double::from_bits(x.to_bits() as u128);
  let loses_info : &mut bool = &mut false;
  IeeeFloat::convert(y, loses_info).value
}

fn sub(x : Quad, y : Quad) -> Quad {
  (x - y).value
}

fn mul(x : Quad, y: Quad) -> Quad {
  (x * y).value
}

fn div(x : Quad, y : Quad) -> Quad {
  (x / y).value
}

pub fn ln_1_minus(f : Quad) -> Quad {
  let one : Quad = Quad::from_i128(1).value;
  let next = | (acc, prev), i | {
    let ii: Quad = Quad::from_i128(i).value;
    let term : Quad = mul(prev, f);
    (sub(acc, div(term, ii)), term)
  };
  (1..30).fold((Quad::ZERO, one), next).0
}

pub fn leader_value(ln1f : Quad, s : Quad) -> Quad {
  let one : Quad = Quad::from_i128(1).value;
  let t0 : Quad = mul(s, ln1f);
  let next = | (acc, prev), i | {
    let ii: Quad = Quad::from_i128(i).value;
    let term : Quad = div(mul(prev, t0), ii);
    (sub(acc, term), term)
  };
  (1..7).fold((Quad::ZERO, one), next).0
}

pub fn leader_check(ln1f : Quad, s : Quad, p : Quad) -> bool {
  p < leader_value(ln1f, s)
}
