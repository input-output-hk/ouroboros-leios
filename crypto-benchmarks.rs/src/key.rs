use blst::min_sig::*;
use num_bigint::BigInt;
use num_rational::Ratio;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::bls_util;
use crate::bls_vote;
use crate::primitive::{arbitrary_poolkeyhash, KesSig, PoolKeyhash};
use crate::util::*;

#[derive(Clone, Debug)]
pub struct SecKey(pub(crate) SecretKey);

impl SecKey {
    pub fn pub_key(&self) -> PubKey {
        PubKey(self.0.sk_to_pk())
    }
}

impl PartialEq for SecKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bytes() == other.0.to_bytes()
    }
}

impl Eq for SecKey {}

impl Serialize for SecKey {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_fixed_bytes(&self.0.to_bytes(), serializer)
    }
}

impl<'de> Deserialize<'de> for SecKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserialize_fixed_bytes(deserializer).and_then(|bytes: [u8; 32]| {
            SecretKey::from_bytes(&bytes)
                .map(SecKey)
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))
        })
    }
}

impl Arbitrary for SecKey {
    fn arbitrary(g: &mut Gen) -> Self {
        let ikm: [u8; 32] = arbitrary_fixed_bytes(g);
        let info: &[u8; 5] = b"Leios";
        SecKey(SecretKey::key_gen(&ikm, info).unwrap())
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct PubKey(pub(crate) PublicKey);

impl Serialize for PubKey {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_fixed_bytes(&self.0.to_bytes(), serializer)
    }
}

impl<'de> Deserialize<'de> for PubKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserialize_fixed_bytes(deserializer).and_then(|bytes: [u8; 96]| {
            PublicKey::from_bytes(&bytes)
                .map(PubKey)
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))
        })
    }
}

impl Arbitrary for PubKey {
    fn arbitrary(g: &mut Gen) -> Self {
        let sk: SecretKey = SecKey::arbitrary(g).0;
        PubKey(sk.sk_to_pk())
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Sig(pub(crate) Signature);

impl Sig {
    pub fn to_rational(&self) -> Ratio<BigInt> {
      bls_util::sig_to_rational(&self.0)
    }
}
impl Serialize for Sig {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_fixed_bytes(&self.0.to_bytes(), serializer)
    }
}

impl<'de> Deserialize<'de> for Sig {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserialize_fixed_bytes(deserializer).and_then(|bytes: [u8; 48]| {
            Signature::from_bytes(&bytes)
                .map(Sig)
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))
        })
    }
}

impl Arbitrary for Sig {
    fn arbitrary(g: &mut Gen) -> Self {
        let msg: [u8; 10] = arbitrary_fixed_bytes(g);
        let dst: [u8; 5] = arbitrary_fixed_bytes(g);
        let aug: [u8; 5] = arbitrary_fixed_bytes(g);
        let sk: SecretKey = SecKey::arbitrary(g).0;
        Sig(sk.sign(&msg, &dst, &aug))
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub struct PoP {
    pub mu1: Sig, // 48 bytes
    pub mu2: Sig, // 48 bytes
} // 96 bytes

impl Arbitrary for PoP {
    fn arbitrary(g: &mut Gen) -> Self {
        let sk: SecretKey = SecKey::arbitrary(g).0;
        let (mu1, mu2) = bls_vote::make_pop(&sk);
        PoP {
            mu1: Sig(mu1),
            mu2: Sig(mu2),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub struct Reg {
    pub pool: PoolKeyhash, //  28 bytes
    pub mvk: PubKey,       //  96 bytes
    pub mu: PoP,           //  96 bytes
    pub kes_sig: KesSig,   // 448 bytes
} // 668 bytes

impl Arbitrary for Reg {
    fn arbitrary(g: &mut Gen) -> Self {
        let sk: SecretKey = SecKey::arbitrary(g).0;
        let (mu1, mu2) = bls_vote::make_pop(&sk);
        Reg {
            pool: arbitrary_poolkeyhash(g),
            mvk: PubKey::arbitrary(g),
            mu: PoP {
                mu1: Sig(mu1),
                mu2: Sig(mu2),
            },
            kes_sig: KesSig::arbitrary(g),
        }
    }
}

pub fn key_gen() -> (SecKey, PubKey, PoP) {
    let sk: SecretKey = bls_vote::gen_key();
    let mvk: PublicKey = sk.sk_to_pk();
    let (mu1, mu2): (Signature, Signature) = bls_vote::make_pop(&sk);
    (
        SecKey(sk),
        PubKey(mvk),
        PoP {
            mu1: Sig(mu1),
            mu2: Sig(mu2),
        },
    )
}

pub fn check_pop(mvk: &PubKey, mu: &PoP) -> bool {
    bls_vote::check_pop(&mvk.0, &mu.mu1.0, &mu.mu2.0)
}
