//! High-level voting operations.

use blst::min_sig::*;
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};

use crate::bls_vote;
use crate::key::{PubKey, SecKey, Sig};
use crate::primitive::{arbitrary_poolkeyhash, CoinFraction, EbHash, Eid, PoolKeyhash};
use crate::registry::*;
use crate::sortition::*;
use crate::util::*;

/// A vote may be either persistent or non-persistent.
/// 
/// Votes occur for an EB `eb` in an election `eid`. The signature `sigma_m` signs the vote.
/// 
/// Persistent voter are identified by their position `persistent` in the table of pools for the epoch.
/// 
/// Non-persistent voters are identified by their pool's key hash. Their `sigma_eid` attests to their presence in the voting committee.
#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub enum Vote {
    Persistent {
        persistent: PersistentId, //   2 bytes
        eid: Eid,                 //   8 bytes
        eb: EbHash,               //  32 bytes
        sigma_m: Sig,             //  48 bytes
    }, //  90 bytes
    Nonpersistent {
        pool: PoolKeyhash, //  28 bytes
        eid: Eid,          //   8 bytes
        eb: EbHash,        //  32 bytes
        sigma_eid: Sig,    //  48 bytes
        sigma_m: Sig,      //  48 bytes
    }, // 164 bytes
}

/// Generate an arbitrary vote, for testing.
impl Arbitrary for Vote {
    fn arbitrary(g: &mut Gen) -> Self {
        let sk: SecretKey = SecKey::arbitrary(g).0;
        let eid: [u8; 8] = arbitrary_fixed_bytes(g);
        let msg: [u8; 10] = arbitrary_fixed_bytes(g);
        if bool::arbitrary(g) {
            let sigma_m = bls_vote::gen_sig(&sk, &eid, &msg);
            Vote::Persistent {
                persistent: PersistentId::arbitrary(g),
                eid: Eid::arbitrary(g),
                eb: EbHash::arbitrary(g),
                sigma_m: Sig(sigma_m),
            }
        } else {
            let (sigma_eid, sigma_m) = bls_vote::gen_vote(&sk, &eid, &msg);
            Vote::Nonpersistent {
                pool: arbitrary_poolkeyhash(g),
                eid: Eid::arbitrary(g),
                eb: EbHash::arbitrary(g),
                sigma_eid: Sig(sigma_eid),
                sigma_m: Sig(sigma_m),
            }
        }
    }
}

/// Sign an election `eid` with a secret key `sk`.
pub fn gen_sigma_eid(eid: &Eid, sk: &SecKey) -> Sig {
    Sig(bls_vote::gen_sigma_eid(&sk.0, &eid.bytes()))
}

/// Create a persistent vote for voter `persistent` for EB `m` in election `eid` using the secret key `sk`.
pub fn gen_vote_persistent(peristent: &PersistentId, eid: &Eid, m: &EbHash, sk: &SecKey) -> Vote {
    let sigma_m = bls_vote::gen_sig(&sk.0, &eid.bytes(), &m.bytes());
    Vote::Persistent {
        persistent: peristent.clone(),
        eid: eid.clone(),
        eb: m.clone(),
        sigma_m: Sig(sigma_m),
    }
}

/// Create a non-persistent vote for voter `pool` for EB `m` in election `eid` using the secret key `sk`.
pub fn gen_vote_nonpersistent(pool: &PoolKeyhash, eid: &Eid, m: &EbHash, sk: &SecKey) -> Vote {
    let (sigma_eid, sigma_m) = bls_vote::gen_vote(&sk.0, &eid.bytes(), &m.bytes());
    Vote::Nonpersistent {
        pool: *pool,
        eid: eid.clone(),
        eb: m.clone(),
        sigma_eid: Sig(sigma_eid),
        sigma_m: Sig(sigma_m),
    }
}

/// Verify a vote `vote` cast with the public key `mvk`.
pub fn verify_vote(mvk: &PubKey, vote: &Vote) -> bool {
    match vote {
        Vote::Persistent {
            persistent: _,
            eid,
            eb,
            sigma_m,
        } => bls_vote::verify_sig(&mvk.0, &eid.bytes(), &eb.bytes(), &sigma_m.0),
        Vote::Nonpersistent {
            pool: _,
            eid,
            eb,
            sigma_eid,
            sigma_m,
        } => bls_vote::verify_vote(&mvk.0, &eid.bytes(), &eb.bytes(), &(sigma_eid.0, sigma_m.0)),
    }
}

/// Cast all of the votes for an election `eid` on an EB `eb` using the voter registry `reg`.
pub fn do_voting(reg: &Registry, eid: &Eid, eb: &EbHash) -> Vec<Vote> {
    let mut votes = Vec::new();
    reg.info.values().for_each(|info| {
        if reg.persistent_id.contains_key(&info.reg.pool) {
            votes.push(gen_vote_persistent(
                &reg.persistent_id[&info.reg.pool],
                eid,
                eb,
                &info.secret,
            ));
        } else if info.stake > 0 {
            let vote = gen_vote_nonpersistent(&info.reg.pool, eid, eb, &info.secret);
            if let Vote::Nonpersistent {
                pool: _,
                eid: _,
                eb: _,
                sigma_eid,
                sigma_m: _,
            } = vote.clone()
            {
                let p = sigma_eid.to_rational();
                let s = CoinFraction::from_coins(info.stake, 1).to_ratio()
                    / reg.nonpersistent_stake.to_ratio();
                if voter_check(reg.voters, &s, &p) > 0 {
                    votes.push(vote);
                }
            }
        }
    });
    votes
}

/// Generate votes for an arbitrary EB in an arbitrary election.
pub fn arbitrary_votes(g: &mut Gen, reg: &Registry) -> Vec<Vote> {
    let eid = Eid::arbitrary(g);
    let eb = EbHash::arbitrary(g);
    do_voting(reg, &eid, &eb)
}
