use blst::min_sig::*;
use pallas::ledger::primitives::Hash;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::bls_vote;
use crate::primitive::{KesSig, PoolKeyhash};
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
        let ikm: [u8; 32]= arbitrary_fixed_bytes(g);
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

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PoP {
    pub mu1: Sig,
    pub mu2: Sig,
}

impl Serialize for PoP {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut bytes: [u8; 96] = [0; 96];
        bytes[0..48].copy_from_slice(&self.mu1.0.to_bytes());
        bytes[48..96].copy_from_slice(&self.mu2.0.to_bytes());
        serialize_fixed_bytes(&bytes, serializer)
    }
}

impl<'de> Deserialize<'de> for PoP {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserialize_fixed_bytes(deserializer).and_then(|bytes: [u8; 96]| {
            let mu1 = Signature::from_bytes(&bytes[0..48])
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))?;
            let mu2 = Signature::from_bytes(&bytes[48..96])
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))?;
            Ok(PoP {
                mu1: Sig(mu1),
                mu2: Sig(mu2),
            })
        })
    }
}

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

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Reg {
    pool: PoolKeyhash,
    mvk: PubKey,
    mu: PoP,
    kes_sig: KesSig,
}

impl Serialize for Reg {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut bytes: [u8; 668] = [0; 668];
        bytes[0..28].copy_from_slice(self.pool.as_slice());
        bytes[28..124].copy_from_slice(&self.mvk.0.to_bytes());
        bytes[124..172].copy_from_slice(&self.mu.mu1.0.to_bytes());
        bytes[172..220].copy_from_slice(&self.mu.mu2.0.to_bytes());
        bytes[220..668].copy_from_slice(&self.kes_sig.0);
        serialize_fixed_bytes(&bytes, serializer)
    }
}

impl<'de> Deserialize<'de> for Reg {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserialize_fixed_bytes(deserializer).and_then(|bytes: [u8; 668]| {
            let pool: PoolKeyhash = Hash::from(&bytes[0..28]);
            let mvk: PublicKey = PublicKey::from_bytes(&bytes[28..124])
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))?;
            let mu1: Signature = Signature::from_bytes(&bytes[124..172])
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))?;
            let mu2: Signature = Signature::from_bytes(&bytes[172..220])
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))?;
            let kes_sig: KesSig = KesSig(bytes[220..668].try_into().unwrap());
            Ok(Reg {
                pool,
                mvk: PubKey(mvk),
                mu: PoP {
                    mu1: Sig(mu1),
                    mu2: Sig(mu2),
                },
                kes_sig,
            })
        })
    }
}
impl Arbitrary for Reg {
    fn arbitrary(g: &mut Gen) -> Self {
        let sk: SecretKey = SecKey::arbitrary(g).0;
        let (mu1, mu2) = bls_vote::make_pop(&sk);
        Reg {
            pool: Hash::from(arbitrary_fixed_bytes(g)),
            mvk: PubKey::arbitrary(g),
            mu: PoP {mu1: Sig(mu1), mu2: Sig(mu2),},
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
