#[macro_use(quickcheck)]
extern crate quickcheck_macros;

use leios_crypto_benchmarks::registry::PersistentId;
use quickcheck::{Arbitrary, Gen};

use leios_crypto_benchmarks::key::{check_pop, key_gen, PoP, PubKey, Reg, SecKey};
use leios_crypto_benchmarks::primitive::{EbHash, Eid};
use leios_crypto_benchmarks::vote::{gen_vote_nonpersistent, gen_vote_persistent, verify_vote};

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
fn prop_verify_vote_persistent(persistent: PersistentId, eid: Eid, m: EbHash, sk: SecKey) -> bool {
    let vote = gen_vote_persistent(&persistent, &eid, &m, &sk);
    let pk = sk.pub_key();
    verify_vote(&pk, &vote)
}

#[quickcheck]
fn prop_verify_vote_nonpersistent(reg: Reg, eid: Eid, m: EbHash, sk: SecKey) -> bool {
    let pool = reg.pool;
    let vote = gen_vote_nonpersistent(&pool, &eid, &m, &sk);
    let pk = sk.pub_key();
    verify_vote(&pk, &vote)
}
