use leios_crypto_benchmarks::sortition::*;
use rustc_apfloat::ieee::Quad;

#[test]
fn leader() {
    let f: Quad = "4.8771764574959465286614323309274434524463393558834E-2"
        .parse::<Quad>()
        .unwrap();
    let f1: Quad = ln_1_minus(f);
    let s: Quad = into_quad(0.001);
    let pexpected: f64 = 1.0
        - (1.0 - 4.877_176_457_495_946_4e-2_f64).powf(0.001_f64);
    assert!(leader_check(f1, s, into_quad(pexpected - 1e-15)));
    assert!(!leader_check(f1, s, into_quad(pexpected + 1e-15)));
}
