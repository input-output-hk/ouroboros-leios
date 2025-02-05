use blst::min_sig::*;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::bls_vote;
use crate::key::{SecKey,Sig};
use crate::util::*;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Cert {
    sigma_tilde_eid: Sig,
    sigma_tilde_m: Sig,
}

impl Serialize for Cert {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut bytes: [u8; 96] = [0; 96];
        bytes[0..48].copy_from_slice(&self.sigma_tilde_eid.0.to_bytes());
        bytes[48..96].copy_from_slice(&self.sigma_tilde_m.0.to_bytes());
        serialize_fixed_bytes(&bytes, serializer)
    }
}

impl<'de> Deserialize<'de> for Cert {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserialize_fixed_bytes(deserializer).and_then(|bytes: [u8; 96]| {
            let sigma_tilde_eid = Signature::from_bytes(&bytes[0..48])
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))?;
            let sigma_tilde_m = Signature::from_bytes(&bytes[48..96])
                .map_err(|_| serde::de::Error::custom("BLST_ERROR"))?;
            Ok(Cert {
                sigma_tilde_eid: Sig(sigma_tilde_eid),
                sigma_tilde_m: Sig(sigma_tilde_m),
            })
        })
    }
}

impl Arbitrary for Cert {
    fn arbitrary(g: &mut Gen) -> Self {
        let sk: SecretKey = SecKey::arbitrary(g).0;
        let eid: [u8; 8] = arbitrary_fixed_bytes(g);
        let msg: [u8; 10] = arbitrary_fixed_bytes(g);
        let (sigma_tilde_eid, sigma_tilde_m) = bls_vote::gen_vote(&sk, &eid, &msg);
        Cert {
            sigma_tilde_eid: Sig(sigma_tilde_eid),
            sigma_tilde_m: Sig(sigma_tilde_m),
        }
    }
}
