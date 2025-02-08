use hex::{FromHex,ToHex};
use pallas::ledger::primitives::{byron::Blake2b256, Hash};
use pallas::ledger::traverse::time::Slot;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::util::*;

pub use pallas::ledger::primitives::PoolKeyhash;

pub fn arbitrary_poolkeyhash(g: &mut Gen) -> PoolKeyhash {
    Hash::from(arbitrary_fixed_bytes(g))
}

pub use pallas::ledger::primitives::Coin;

pub fn arbitrary_coin(g: &mut Gen) -> Coin {
    u64::arbitrary(g) % 2000000000000
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Eid(pub Slot);

impl Eid {

pub fn parse(s: &str) -> Result<Self, String> {
    let value = s.parse::<u64>()
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
        let bytes = Vec::<u8>::from_hex(s)
          .map_err(|e| format!("Invalid hex bytes: {}", e))?;
        if bytes.len()!= 32 {
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
