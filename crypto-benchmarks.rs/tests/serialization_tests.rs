//! Round-trip serialization tests.

#[macro_use(quickcheck)]
extern crate quickcheck_macros;

use serde::{de::DeserializeOwned, Serialize};

use leios_crypto_benchmarks::cert::Cert;
use leios_crypto_benchmarks::key::{PoP, PubKey, Reg, SecKey, Sig};
use leios_crypto_benchmarks::primitive::{EbHash, Eid, KesSig};
use leios_crypto_benchmarks::vote::Vote;

fn prop_serialization<A>(expected: A) -> bool
where
    A: Serialize + DeserializeOwned + PartialEq, // Ensure A can be serialized, deserialized, and compared
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
