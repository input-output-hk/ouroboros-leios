use hex::{FromHex, ToHex};
use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::FromPrimitive;
use pallas::ledger::primitives::{byron::Blake2b256, Hash};
use pallas::ledger::traverse::time::Slot;
use quickcheck::{Arbitrary, Gen};
use rand::prelude::Distribution;
use rand::rngs::StdRng;
use rand::SeedableRng;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use statrs::distribution::ContinuousCDF;
use statrs::distribution::{Beta, Uniform};
use std::collections::BTreeMap;

use crate::util::*;

pub use pallas::ledger::primitives::PoolKeyhash;

pub fn arbitrary_poolkeyhash(g: &mut Gen) -> PoolKeyhash {
    Hash::from(arbitrary_fixed_bytes(g))
}

pub use pallas::ledger::primitives::Coin;

pub fn arbitrary_coin(g: &mut Gen) -> Coin {
    u64::arbitrary(g) % 999999 + 1
}

pub(crate) fn realistic_stake_dist(g: &mut Gen, total: u64, n: usize) -> Vec<Coin> {
    let rng = &mut StdRng::seed_from_u64(u64::arbitrary(g));
    let noise = Uniform::new(0.75, 1.25).unwrap();
    let beta = Beta::new(11f64, 1f64).unwrap();
    let cum: Vec<f64> = (0..n)
        .map(|i| beta.cdf((i as f64) / (total as f64)))
        .collect();
    let dif: Vec<f64> = (1..n)
        .map(|i| (cum[i] - cum[i - 1]) * noise.sample(rng))
        .collect();
    let scale: f64 = (total as f64) / dif.iter().sum::<f64>();
    dif.iter()
        .map(|coin| (scale * *coin).round() as Coin)
        .collect()
}

pub fn arbitrary_stake_distribution(
    g: &mut Gen,
    total: u64,
    n: usize,
) -> BTreeMap<PoolKeyhash, Coin> {
    BTreeMap::from_iter(
        realistic_stake_dist(g, total, n)
            .iter()
            .map(|coin| (arbitrary_poolkeyhash(g), *coin)),
    )
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct CoinFraction(pub Ratio<BigInt>);

impl CoinFraction {
    pub fn from_coins(part: Coin, whole: Coin) -> Self {
        CoinFraction(Ratio::new(
            BigInt::from_u64(part).unwrap(),
            BigInt::from_u64(whole).unwrap(),
        ))
    }

    pub fn to_ratio(&self) -> Ratio<BigInt> {
        self.0.clone()
    }
}

impl Serialize for CoinFraction {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        (self.0.numer(), self.0.denom()).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for CoinFraction {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (num, den) = <(BigInt, BigInt)>::deserialize(deserializer)?;
        Ok(CoinFraction(Ratio::new(num, den)))
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Eid(pub Slot);

impl Eid {
    pub fn parse(s: &str) -> Result<Self, String> {
        let value = s
            .parse::<u64>()
            .map_err(|e| format!("Invalid Eid: {}", e))?;
        Ok(Eid(value))
    }

    pub fn bytes(&self) -> [u8; 8] {
        u64::to_be_bytes(self.0)
    }
}

impl Serialize for Eid {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let bytes: [u8; 8] = u64::to_be_bytes(self.0);
        serialize_fixed_bytes(&bytes, serializer)
    }
}

impl<'de> Deserialize<'de> for Eid {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserialize_fixed_bytes(deserializer).map(|bytes: [u8; 8]| Eid(u64::from_be_bytes(bytes)))
    }
}

impl Arbitrary for Eid {
    fn arbitrary(g: &mut Gen) -> Self {
        Eid(u64::arbitrary(g))
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct EbHash(pub(crate) Blake2b256);

impl EbHash {
    pub fn bytes(&self) -> [u8; 32] {
        self.0.as_slice().try_into().unwrap()
    }

    pub fn parse(s: &str) -> Result<Self, String> {
        let bytes = Vec::<u8>::from_hex(s).map_err(|e| format!("Invalid hex bytes: {}", e))?;
        if bytes.len() != 32 {
            return Err("Incorrect byte length: must be 32 bytes".to_string());
        }
        let mut array = [0u8; 32];
        array.copy_from_slice(&bytes);
        Ok(EbHash(Hash::new(array)))
    }
}

impl ToHex for EbHash {
    fn encode_hex<T: std::iter::FromIterator<char>>(&self) -> T {
        self.0.encode_hex()
    }
    fn encode_hex_upper<T: std::iter::FromIterator<char>>(&self) -> T {
        self.0.encode_hex_upper()
    }
}

impl Serialize for EbHash {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let bytes: [u8; 32] = self.0.as_slice().try_into().unwrap();
        serialize_fixed_bytes(&bytes, serializer)
    }
}

impl<'de> Deserialize<'de> for EbHash {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserialize_fixed_bytes(deserializer).map(|bytes: [u8; 32]| EbHash(Hash::from(bytes)))
    }
}

impl Arbitrary for EbHash {
    fn arbitrary(g: &mut Gen) -> Self {
        EbHash(Hash::from(arbitrary_fixed_bytes(g)))
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct KesSig(pub(crate) [u8; 448]);

impl KesSig {
    pub fn null() -> Self {
        KesSig([0; 448])
    }
}
impl Serialize for KesSig {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_fixed_bytes(&self.0, serializer)
    }
}

impl<'de> Deserialize<'de> for KesSig {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserialize_fixed_bytes(deserializer).map(KesSig)
    }
}

impl Arbitrary for KesSig {
    fn arbitrary(g: &mut Gen) -> Self {
        KesSig(arbitrary_fixed_bytes(g))
    }
}
