use blst::min_sig::*;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashSet};

use crate::bls_vote;
use crate::key::{PubKey, Sig};
use crate::primitive::{EbHash, Eid, PoolKeyhash};
use crate::registry::*;
use crate::vote::*;

#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub struct Cert {
    eid: Eid,
    eb: EbHash,
    persistent_voters: HashSet<PersistentId>,
    nonpersistent_voters: BTreeMap<PoolKeyhash, Sig>,
    sigma_tilde_eid: Option<Sig>,
    sigma_tilde_m: Sig,
}

pub fn arbitrary_cert(g: &mut Gen, reg: &Registry) -> Cert {
    let eid = Eid::arbitrary(g);
    let eb = EbHash::arbitrary(g);
    gen_cert(&reg, &do_voting(&reg, &eid, &eb)).unwrap()
}

impl Arbitrary for Cert {
    fn arbitrary(g: &mut Gen) -> Self {
        let reg = Registry::arbitrary(g);
        arbitrary_cert(g, &reg)
    }
}

#[derive(Default)]
struct TraverseVote<'a> {
    pub eids: HashSet<&'a Eid>,
    pub ebs: HashSet<&'a EbHash>,
    pub ps: HashSet<PersistentId>,
    pub nps: BTreeMap<PoolKeyhash, Sig>,
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
            reg.persistent_pool.get(persistent).map(|_| ())
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
            reg.info.get(pool).map(|_| ())
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
    if t.sigma_eids.len() > 0 {
        let (sigma_tilde_eid, sigma_tilde_m) =
            bls_vote::gen_cert_fa(&t.sigma_eids, &t.sigma_ms).ok()?;
        Some(Cert {
            eid: eid.clone(),
            eb: eb.clone(),
            persistent_voters: t.ps,
            nonpersistent_voters: t.nps,
            sigma_tilde_eid: Some(Sig(sigma_tilde_eid)),
            sigma_tilde_m: Sig(sigma_tilde_m),
        })
    } else {
        let sigma_tilde_m = bls_vote::gen_cert_fa_pure(&t.sigma_ms).ok()?;
        Some(Cert {
            eid: eid.clone(),
            eb: eb.clone(),
            persistent_voters: t.ps,
            nonpersistent_voters: t.nps,
            sigma_tilde_eid: None,
            sigma_tilde_m: Sig(sigma_tilde_m),
        })
    }
}

pub fn verify_cert(reg: &Registry, cert: &Cert) -> bool {
    let pks_persistent: Vec<&PublicKey> = cert
        .persistent_voters
        .iter()
        .map(|pool| &reg.info[&reg.persistent_pool[pool]].reg.mvk.0)
        .collect();
    let pks_nonpersistent: Vec<&PublicKey> = cert
        .nonpersistent_voters
        .keys()
        .map(|pool| &reg.info[pool].reg.mvk.0)
        .collect();
    let mut pks: Vec<&PublicKey> = Vec::new();
    pks.extend(pks_persistent);
    pks.extend(pks_nonpersistent.clone());
    let sigma_eids: Vec<&Signature> = cert
        .nonpersistent_voters
        .values()
        .map(|sig| &sig.0)
        .collect();
    match cert.sigma_tilde_eid.clone() {
        Some(sigma_tilde_eid) => bls_vote::verify_cert_fa(
            &pks,
            &pks_nonpersistent,
            &cert.eid.bytes(),
            &cert.eb.bytes(),
            &sigma_eids,
            &sigma_tilde_eid.0,
            &cert.sigma_tilde_m.0,
        ),
        None => {
            cert.nonpersistent_voters.is_empty()
                && bls_vote::verify_cert_fa_pure(
                    &pks,
                    &cert.eid.bytes(),
                    &cert.eb.bytes(),
                    &cert.sigma_tilde_m.0,
                )
        }
    }
}
