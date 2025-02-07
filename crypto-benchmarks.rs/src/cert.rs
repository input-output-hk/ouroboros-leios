use blst::min_sig::*;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::bls_vote;
use crate::key::{PubKey, SecKey, Sig};
use crate::primitive::{EbHash, Eid, PoolKeyhash};
use crate::registry::*;
use crate::util::*;
use crate::vote::Vote;

#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub struct Cert {
    eid: Eid,
    eb: EbHash,
    persistent_voters: HashSet<PersistentId>,
    nonpersistent_voters: HashMap<PoolKeyhash, Sig>,
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
            persistent_voters: HashSet::new(),
            nonpersistent_voters: HashMap::new(),
            sigma_tilde_eid: Sig(sigma_tilde_eid),
            sigma_tilde_m: Sig(sigma_tilde_m),
        }
    }
}

#[derive(Default)]
struct TraverseVote<'a> {
    pub eids: HashSet<&'a Eid>,
    pub ebs: HashSet<&'a EbHash>,
    pub ps: HashSet<PersistentId>,
    pub nps: HashMap<PoolKeyhash, Sig>,
    pub mvks: Vec<&'a PubKey>,
    pub sigma_eids: Vec<&'a Signature>,
    pub sigma_ms: Vec<&'a Signature>,
}

fn traverse_vote<'a>(reg: &'a Registry, t: &mut TraverseVote<'a>, vote: &'a Vote) -> Option<()> {
    match vote {
        Vote::Persistent {
            persistent,
            eid,
            eb,
            sigma_m,
        } => {
            t.eids.insert(eid);
            t.ebs.insert(eb);
            t.ps.insert(persistent.clone());
            t.sigma_ms.push(&sigma_m.0);
            reg.persistent.get(persistent).map(|_| ())
        }
        Vote::Nonpersistent {
            pool,
            eid,
            eb,
            sigma_eid,
            sigma_m,
        } => {
            t.eids.insert(eid);
            t.ebs.insert(eb);
            t.nps.insert(*pool, sigma_eid.clone());
            t.sigma_eids.push(&sigma_eid.0);
            t.sigma_ms.push(&sigma_m.0);
            reg.info.get(pool).map(|info| t.mvks.push(&info.reg.mvk))
        }
    }
}

fn unique<X>(xs: &HashSet<X>) -> Option<&X> {
    if xs.len() == 1 {
        xs.iter().next()
    } else {
        None
    }
}

pub fn gen_cert(reg: &Registry, votes: &[Vote]) -> Option<Cert> {
    let mut t: TraverseVote = TraverseVote::default();
    let _ = votes
        .iter()
        .try_for_each(|vote| traverse_vote(reg, &mut t, vote));
    let eid: &Eid = unique(&t.eids)?;
    let eb: &EbHash = unique(&t.ebs)?;
    let (sigma_tilde_eid, sigma_tilde_m) =
        bls_vote::gen_cert_fa(&t.sigma_eids, &t.sigma_ms).ok()?;
    Some(Cert {
        eid: eid.clone(),
        eb: eb.clone(),
        persistent_voters: t.ps,
        nonpersistent_voters: t.nps,
        sigma_tilde_eid: Sig(sigma_tilde_eid),
        sigma_tilde_m: Sig(sigma_tilde_m),
    })
}
