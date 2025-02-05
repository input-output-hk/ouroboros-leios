use blst::min_sig::*;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::bls_vote;
use crate::key::{SecKey, Sig};
use crate::primitive::{EbHash, Eid, PoolKeyhash};
use crate::registry::PersistentId;
use crate::util::*;
use crate::vote::Vote;

#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub struct Cert {
    eid: Eid,
    eb: EbHash,
    persistent_voters: HashMap<PersistentId, Sig>,
    nonpersistent_voters: HashMap<PoolKeyhash, Vote>,
    sigma_tilde_eid: Sig,
    sigma_tilde_m: Sig,
}

impl Arbitrary for Cert {
    fn arbitrary(g: &mut Gen) -> Self {
        let sk: SecretKey = SecKey::arbitrary(g).0;
        let eid: [u8; 8] = arbitrary_fixed_bytes(g);
        let msg: [u8; 10] = arbitrary_fixed_bytes(g);
        let (sigma_tilde_eid, sigma_tilde_m) = bls_vote::gen_vote(&sk, &eid, &msg);
        Cert {
            eid: Eid::arbitrary(g),
            eb: EbHash::arbitrary(g),
            persistent_voters: HashMap::new(),
            nonpersistent_voters: HashMap::new(),
            sigma_tilde_eid: Sig(sigma_tilde_eid),
            sigma_tilde_m: Sig(sigma_tilde_m),
        }
    }
}
