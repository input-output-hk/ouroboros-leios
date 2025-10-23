//! Quickcheck tests for certificates.

#[macro_use(quickcheck)]
extern crate quickcheck_macros;

use quickcheck::Arbitrary;

use leios_crypto_benchmarks::cert::{gen_cert, verify_cert, weigh_cert};
use leios_crypto_benchmarks::registry::Registry;
use leios_crypto_benchmarks::vote::{arbitrary_votes, Vote};

#[derive(Clone, Debug)]
struct CertScenario {
    pub reg: Registry,
    pub votes: Vec<Vote>,
}

impl Arbitrary for CertScenario {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let reg = Registry::arbitrary(g);
        let votes = arbitrary_votes(g, &reg);
        CertScenario { reg, votes }
    }
}

#[quickcheck]
fn prop_gen_cert(scenario: CertScenario) -> bool {
    gen_cert(&scenario.reg, &scenario.votes).is_some()
}

#[quickcheck]
fn prop_verify_cert(scenario: CertScenario) -> bool {
    match gen_cert(&scenario.reg, &scenario.votes) {
        Some(cert) => verify_cert(&scenario.reg, &cert),
        None => false,
    }
}

#[quickcheck]
fn prop_weigh_cert(scenario: CertScenario) -> bool {
    match gen_cert(&scenario.reg, &scenario.votes) {
        Some(cert) => weigh_cert(&scenario.reg, &cert).is_some(),
        None => false,
    }
}
