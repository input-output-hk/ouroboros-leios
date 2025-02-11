#[macro_use(quickcheck)]
extern crate quickcheck_macros;

use leios_crypto_benchmarks::cert::*;
use leios_crypto_benchmarks::registry::*;
use leios_crypto_benchmarks::vote::*;
use quickcheck::Arbitrary;

#[derive(Clone, Debug)]
struct CertScenario {
  pub reg: Registry,
  pub votes: Vec<Vote>,
}


impl Arbitrary for CertScenario {
  fn arbitrary(g: &mut quickcheck::Gen) -> Self {
      let reg = Registry::arbitrary(g);
      let votes = arbitrary_votes(g, &reg);
      CertScenario {reg, votes}
  }
}

#[quickcheck]
fn prop_gen_cert(scenario: CertScenario) -> bool {
  gen_cert(&scenario.reg, &scenario.votes).is_some()
}

#[quickcheck]
fn prop_verify_cert(scenario: CertScenario) -> bool {
  match gen_cert(&scenario.reg, &scenario.votes) {
    Some(cert) => {verify_cert(&scenario.reg, &cert)}
    None => {false}
  }
}

#[quickcheck]
fn prop_weigh_cert(scenario: CertScenario) -> bool {
  match gen_cert(&scenario.reg, &scenario.votes) {
    Some(cert) => {weigh_cert(&scenario.reg, &cert).is_some()}
    None => {false}
  }
}
