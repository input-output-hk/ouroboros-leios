
use leios_crypto_benchmarks::sortition::*;
use rustc_apfloat::ieee::Quad;


fn main() {

    let f : Quad = "4.8771764574959465286614323309274434524463393558834E-2".parse::<Quad>().unwrap();
    let f1 : Quad = ln_1_minus(f);
    let s : Quad = into_quad(0.001);
    let p : f64 = 1.0 - (1.0 - 4.8771764574959465286614323309274434524463393558834e-2 as f64).powf(0.001 as f64);
    let p0 : Quad = into_quad(p - 1e-15);
    let p1 : Quad = into_quad(p + 1e-15);
    println!("ln(1 - f) = {} vs {}", (1.0 - 4.8771764574959465286614323309274434524463393558834e-2 as f64).ln(), f1);
    println!("1 - (1 -f)^s = {} vs {} ", p, leader_value(f1, s));
    println!("Lower: {}", leader_check(f1, s, p0));
    println!("Upper: {}", leader_check(f1, s, p1));

    let votes : Quad = into_quad(500.0);
    let mut pv : Quad = into_quad(0.0);
    loop {
      pv = (pv + into_quad(0.01)).value;
      if pv > into_quad(1.0) {
        break;
      }
      println!("{} {}", pv, voter_check(votes, s, pv))
    }
}