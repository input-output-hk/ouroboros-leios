use pallas_primitives::{Hash,PoolKeyhash};
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::bls::*;
use crate::util::*;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct KesSignature(pub [u8; 448]);

impl Serialize for KesSignature {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
      S: Serializer,
  {
      serialize_fixed_bytes(&self.0, serializer)
  }
}

impl<'de> Deserialize<'de> for KesSignature {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
      D: Deserializer<'de>,
  {
    deserialize_fixed_bytes(deserializer).map(KesSignature)
  }
}

impl Arbitrary for KesSignature {
  fn arbitrary(g: &mut Gen) -> Self {
      KesSignature(arbitrary_fixed_bytes(g))
  }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Registration {
  pool: PoolKeyhash,            // 28 bytes
  mvk: BlsKey,                  // 96 bytes (compressed)
  mu: (BlsSig, BlsSig),         // 2x48 bytes (compressed)
  kes_signature: KesSignature,  // 448 bytes
}

impl Serialize for Registration {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
      where
          S: Serializer,
           {
      let mut bytes : [u8; 668] = [0; 668];
      bytes[0..28].copy_from_slice(self.pool.as_slice());
      bytes[28..124].copy_from_slice(&self.mvk.0);
      bytes[124..172].copy_from_slice(&self.mu.0.0);
      bytes[172..220].copy_from_slice(&self.mu.1.0);
      bytes[220..668].copy_from_slice(&self.kes_signature.0);
      serialize_fixed_bytes(&bytes, serializer)
  }
}
impl Arbitrary for Registration {
  fn arbitrary(g: &mut Gen) -> Self {
      Registration {
        pool : Hash::from(arbitrary_fixed_bytes(g)),
        mvk: BlsKey::arbitrary(g),
        mu: (BlsSig::arbitrary(g), BlsSig::arbitrary(g)),
        kes_signature: KesSignature::arbitrary(g),
      }
  }
}