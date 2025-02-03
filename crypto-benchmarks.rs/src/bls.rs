use blst::min_sig::*;
use blst::*;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::util::*;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct BlsKey(pub [u8; 96]);

impl BlsKey {

    pub fn from_point(pk: &PublicKey) -> Self {
       let pk_bytes: [u8; 96] = pk.to_bytes();
       BlsKey(pk_bytes)
    }

    pub fn to_point(&self) -> Result<PublicKey, BLST_ERROR> {
        PublicKey::from_bytes(&self.0)
    }

}

impl Serialize for BlsKey {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_fixed_bytes(&self.0, serializer)
    }
  }
  
  impl<'de> Deserialize<'de> for BlsKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
      deserialize_fixed_bytes(deserializer).map(BlsKey)
    }
  }

impl Arbitrary for BlsKey {
    fn arbitrary(g: &mut Gen) -> Self {
        BlsKey(arbitrary_fixed_bytes(g))
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct BlsSig(pub [u8; 48]);

impl BlsSig {

    pub fn from_point(sig: &Signature) -> Self {
        let sig_bytes: [u8; 48] = sig.to_bytes();
        BlsSig(sig_bytes)
    }

    pub fn to_point(&self) -> Result<Signature, BLST_ERROR> {
        Signature::from_bytes(&self.0)
    }

}

impl Serialize for BlsSig {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_fixed_bytes(&self.0, serializer)
    }
  }
  
  impl<'de> Deserialize<'de> for BlsSig{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
      deserialize_fixed_bytes(deserializer).map(BlsSig)
    }
  }
  
pub fn pk_transform(f: &dyn Fn(blst_p2) -> blst_p2, pk: &PublicKey) -> PublicKey {
    let mut point: blst_p2 = blst_p2::default();
    unsafe {
        let pk_bytes: [u8; 192] = pk.serialize();
        let mut point_aff: blst_p2_affine = blst_p2_affine::default();
        blst_p2_deserialize(&mut point_aff, pk_bytes.as_ptr());
        blst_p2_from_affine(&mut point, &point_aff);
    }

    let point1: blst_p2 = f(point);

    unsafe {
        let mut point1_aff: blst_p2_affine = blst_p2_affine::default();
        blst_p2_to_affine(&mut point1_aff, &point1);
        let mut pk1_bytes: [u8; 192] = [0; 192];
        blst_p2_affine_serialize(pk1_bytes.as_mut_ptr(), &point1_aff);
        PublicKey::deserialize(&pk1_bytes).unwrap()
    }
}

pub fn sig_transform(f: &dyn Fn(blst_p1) -> blst_p1, sig: &Signature) -> Signature {
    let mut point: blst_p1 = blst_p1::default();
    unsafe {
        let sig_bytes: [u8; 96] = sig.serialize();
        let mut point_aff: blst_p1_affine = blst_p1_affine::default();
        blst_p1_deserialize(&mut point_aff, sig_bytes.as_ptr());
        blst_p1_from_affine(&mut point, &point_aff);
    }

    let point1: blst_p1 = f(point);

    unsafe {
        let mut point1_aff: blst_p1_affine = blst_p1_affine::default();
        blst_p1_to_affine(&mut point1_aff, &point1);
        let mut sig1_bytes: [u8; 96] = [0; 96];
        blst_p1_affine_serialize(sig1_bytes.as_mut_ptr(), &point1_aff);
        Signature::deserialize(&sig1_bytes).unwrap()
    }
}

impl Arbitrary for BlsSig {
    fn arbitrary(g: &mut Gen) -> Self {
        BlsSig(arbitrary_fixed_bytes(g))
    }
}