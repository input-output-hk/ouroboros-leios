#[macro_use(quickcheck)]
extern crate quickcheck_macros;

use quickcheck::{Arbitrary, Gen};

use leios_crypto_benchmarks::api::*;

#[derive(Clone, Debug)]
struct PopScenario {
    mvk: PubKey,
    mu: PoP,
}

impl Arbitrary for PopScenario {
    fn arbitrary(_: &mut Gen) -> Self {
        let (_, mvk, mu) = key_gen();
        PopScenario { mvk, mu }
    }
}

#[quickcheck]
fn prop_check_pop(kgo: PopScenario) -> bool {
    check_pop(&kgo.mvk, &kgo.mu)
}

#[quickcheck]
fn prop_verify_vote(eid: Eid, m: EbHash, sk: SecKey) -> bool {
    let vote = gen_vote(&eid, &m, &sk);
    let pk = sk.pub_key();
    verify_vote(&eid, &m, &pk, &vote)
}
