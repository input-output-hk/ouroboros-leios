#[macro_use(quickcheck)]
extern crate quickcheck_macros;

use quickcheck::{Arbitrary, Gen};
use serde::{Serialize, de::DeserializeOwned};

use leios_crypto_benchmarks::api::*;

fn prop_serialization<A>(expected: A) -> bool
where
    A: Serialize + DeserializeOwned + PartialEq,  // Ensure A can be serialized, deserialized, and compared
{
    let bytes = serde_cbor::to_vec(&expected).unwrap();
    let actual: A = serde_cbor::from_slice(&bytes).unwrap();
    expected == actual
}

#[quickcheck]
fn prop_eid_serialization(expected: Eid) -> bool {
    prop_serialization(expected)
}

#[quickcheck]
fn prop_ebhash_serialization(expected: EbHash) -> bool {
  prop_serialization(expected)
}

#[quickcheck]
fn prop_seckey_serialization(expected: SecKey) -> bool {
  prop_serialization(expected)
}

#[quickcheck]
fn prop_pubkey_serialization(expected: PubKey) -> bool {
  prop_serialization(expected)
}

#[quickcheck]
fn prop_sig_serialization(expected: Sig) -> bool {
  prop_serialization(expected)
}

#[quickcheck]
fn prop_pop_serialization(expected: PoP) -> bool {
  prop_serialization(expected)
}

#[quickcheck]
fn prop_kessig_serialization(expected: KesSig) -> bool {
  prop_serialization(expected)
}

#[quickcheck]
fn prop_reg_serialization(expected: Reg) -> bool {
  prop_serialization(expected)
}

#[quickcheck]
fn prop_vote_serialization(expected: Vote) -> bool {
  prop_serialization(expected)
}

#[quickcheck]
fn prop_cert_serialization(expected: Cert) -> bool {
  prop_serialization(expected)
}

#[derive(Clone, Debug)]
struct PopScenario {
  sk: SecKey,
  mvk: PubKey,
  mu: PoP,
}

impl Arbitrary for PopScenario {
  fn arbitrary(_: &mut Gen) -> Self {
      let (sk, mvk, mu) = key_gen();
      PopScenario{sk, mvk, mu,}
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