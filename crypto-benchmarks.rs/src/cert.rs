use blst::min_sig::*;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashSet};

use crate::bls_vote;
use crate::key::Sig;
use crate::primitive::{Coin, CoinFraction, EbHash, Eid, PoolKeyhash};
use crate::registry::*;
use crate::sortition::voter_check;
use crate::vote::*;

#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub struct Cert {
    pub eid: Eid,
    pub eb: EbHash,
    pub persistent_voters: HashSet<PersistentId>,
    pub nonpersistent_voters: BTreeMap<PoolKeyhash, Sig>,
    pub sigma_tilde_eid: Option<Sig>,
    pub sigma_tilde_m: Sig,
}

pub fn arbitrary_cert(g: &mut Gen, reg: &Registry) -> Cert {
    let eid = Eid::arbitrary(g);
    let eb = EbHash::arbitrary(g);
    gen_cert(reg, &do_voting(reg, &eid, &eb)).unwrap()
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
    if !t.sigma_eids.is_empty() {
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

fn weigh_persistent(reg: &Registry, cert: &Cert) -> Option<CoinFraction> {
    let weight: Option<Coin> =
      cert.persistent_voters
      .iter()
      .fold(Some(0), |acc, pid| 
        reg.persistent_pool.get(pid)
          .and_then(|pool|
                acc.map(|total| total + reg.info[pool].stake))
          );
    weight.map(|total| CoinFraction::from_coins(total, 1))
}

fn weigh_nonpersistent(reg: &Registry, cert: &Cert) -> Option<CoinFraction> {
    let nonpersistent_voters = reg.voters - cert.persistent_voters.len();
    let weight: Option<usize> =
      cert.nonpersistent_voters
        .iter()
        .fold(Some(0),|acc, (pool, sigma_eid)|
            reg.info.get(pool)
              .and_then(|info|
                acc.map(|total| {
                    let p = sigma_eid.to_rational();
                    let s = CoinFraction::from_coins(info.stake, reg.total_stake).to_ratio()
                    / reg.nonpersistent_stake.to_ratio();
                    total + voter_check(nonpersistent_voters, &s, &p)
                })
            )
        );
    weight.map(|total|
        CoinFraction(
            CoinFraction::from_coins(total as u64 , nonpersistent_voters as u64).to_ratio()
              * reg.nonpersistent_stake.to_ratio()
        )
    )
}

pub fn weigh_cert(reg: &Registry, cert: &Cert) -> Option<CoinFraction> {
    let persistent_weight = weigh_persistent(reg, cert)?.to_ratio();
    let nonpersistent_weight = weigh_nonpersistent(reg, cert)?.to_ratio();
    Some(CoinFraction(
        (persistent_weight + nonpersistent_weight)
          * CoinFraction::from_coins(1, reg.total_stake).to_ratio()
    ))
}