use blst::min_sig::*;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::bls_vote;
use crate::key::{PubKey, SecKey, Sig};
use crate::primitive::{EbHash, Eid};
use crate::util::*;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Vote {
    sigma_eid: Sig,
    sigma_m: Sig,
}

impl Serialize for Vote {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut bytes: [u8; 96] = [0; 96];
        bytes[0..48].copy_from_slice(&self.sigma_eid.0.to_bytes());
        bytes[48..96].copy_from_slice(&self.sigma_m.0.to_bytes());
        serialize_fixed_bytes(&bytes, serializer)
    }
}

impl<'de> Deserialize<'de> for Vote {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserialize_fixed_bytes(deserializer).and_then(|bytes: [u8; 96]| {
            let sigma_eid = Signature::from_bytes(&bytes[0..48])
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))?;
            let sigma_m = Signature::from_bytes(&bytes[48..96])
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))?;
            Ok(Vote {
                sigma_eid: Sig(sigma_eid),
                sigma_m: Sig(sigma_m),
            })
        })
    }
}

impl Arbitrary for Vote {
    fn arbitrary(g: &mut Gen) -> Self {
        let sk: SecretKey = SecKey::arbitrary(g).0;
        let eid: [u8; 8] = arbitrary_fixed_bytes(g);
        let msg: [u8; 10] = arbitrary_fixed_bytes(g);
        let (sigma_eid, sigma_m) = bls_vote::gen_vote(&sk, &eid, &msg);
        Vote {
            sigma_eid: Sig(sigma_eid),
            sigma_m: Sig(sigma_m),
        }
    }
}

pub fn gen_vote(eid: &Eid, m: &EbHash, sk: &SecKey) -> Vote {
    let (sigma_eid, sigma_m) = bls_vote::gen_vote(&sk.0, &eid.bytes(), &m.bytes());
    Vote {
        sigma_eid: Sig(sigma_eid),
        sigma_m: Sig(sigma_m),
    }
}

pub fn verify_vote(eid: &Eid, m: &EbHash, mvk: &PubKey, vote: &Vote) -> bool {
    bls_vote::verify_vote(
        &mvk.0,
        &eid.bytes(),
        &m.bytes(),
        &(vote.sigma_eid.0, vote.sigma_m.0),
    )
}
