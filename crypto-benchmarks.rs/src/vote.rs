use blst::min_sig::*;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};

use crate::bls_vote;
use crate::key::{PubKey, SecKey, Sig};
use crate::primitive::{arbitrary_poolkeyhash, EbHash, Eid, PoolKeyhash};
use crate::util::*;

#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub struct Vote {
    pool: PoolKeyhash, //  28 bytes
    eid: Eid,          //   8 bytes
    eb: EbHash,        //  32 bytes
    sigma_eid: Sig,    //  48 bytes
    sigma_m: Sig,      //  48 bytes
}                      // 164 bytes

impl Arbitrary for Vote {
    fn arbitrary(g: &mut Gen) -> Self {
        let sk: SecretKey = SecKey::arbitrary(g).0;
        let eid: [u8; 8] = arbitrary_fixed_bytes(g);
        let msg: [u8; 10] = arbitrary_fixed_bytes(g);
        let (sigma_eid, sigma_m) = bls_vote::gen_vote(&sk, &eid, &msg);
        Vote {
            pool: arbitrary_poolkeyhash(g),
            eid: Eid::arbitrary(g),
            eb: EbHash::arbitrary(g),
            sigma_eid: Sig(sigma_eid),
            sigma_m: Sig(sigma_m),
        }
    }
}

pub fn gen_vote(pool: &PoolKeyhash, eid: &Eid, m: &EbHash, sk: &SecKey) -> Vote {
    let (sigma_eid, sigma_m) = bls_vote::gen_vote(&sk.0, &eid.bytes(), &m.bytes());
    Vote {
        pool: *pool,
        eid: eid.clone(),
        eb: m.clone(),
        sigma_eid: Sig(sigma_eid),
        sigma_m: Sig(sigma_m),
    }
}

pub fn verify_vote(mvk: &PubKey, vote: &Vote) -> bool {
    bls_vote::verify_vote(
        &mvk.0,
        &vote.eid.bytes(),
        &vote.eb.bytes(),
        &(vote.sigma_eid.0, vote.sigma_m.0),
    )
}
