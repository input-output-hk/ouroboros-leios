//! Operations on the voter registry.

use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

use crate::fait_accompli::FaSortition;
use crate::key::{arbitrary_reg, Reg, SecKey};
use crate::primitive::{
    arbitrary_coin, arbitrary_poolkeyhash, arbitrary_stake_distribution, Coin, CoinFraction,
    PoolKeyhash,
};
use crate::realism::realistic_voters;

/// A persistent identifier is just an integer identifying the epoch's pools.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug, Serialize, Deserialize)]
pub struct PersistentId(pub u16);

impl Arbitrary for PersistentId {
    fn arbitrary(g: &mut Gen) -> Self {
        PersistentId(u16::arbitrary(g))
    }
}

/// Pools are tracked by their secret key `secret`, their public registration information `reg`, and the amount of stake `stake` they have at the start of the epoch.
#[derive(PartialEq, Eq, Clone, Debug, Serialize, Deserialize)]
pub struct PoolInfo {
    /// The secret key.
    pub secret: SecKey,
    /// The public registration.
    pub reg: Reg,
    /// The stake for the epoch.
    pub stake: Coin,
}

impl Arbitrary for PoolInfo {
    fn arbitrary(g: &mut Gen) -> Self {
        let secret = SecKey::arbitrary(g);
        let pool = arbitrary_poolkeyhash(g);
        PoolInfo {
            reg: arbitrary_reg(g, &pool, &secret),
            stake: arbitrary_coin(g),
            secret,
        }
    }
}

/// Generate an arbitrary array of pools from the stake distribution `stake`.
pub fn arbitrary_pools(g: &mut Gen, stake: &BTreeMap<PoolKeyhash, Coin>) -> Vec<PoolInfo> {
    stake
        .iter()
        .map(|(pool, coin)| {
            let secret = SecKey::arbitrary(g);
            PoolInfo {
                reg: arbitrary_reg(g, pool, &secret),
                stake: *coin,
                secret,
            }
        })
        .collect()
}

/// The voter registry records which pools are persistent vs non-persistent and their private and public registration information, along with the number of voters and amount of stake.
#[derive(PartialEq, Eq, Clone, Debug, Serialize, Deserialize)]
pub struct Registry {
    /// Private and public data for the pools.
    pub info: BTreeMap<PoolKeyhash, PoolInfo>,
    /// Lookup table of pool key hashes for the persistent voters.
    pub persistent_pool: BTreeMap<PersistentId, PoolKeyhash>,
    /// Lookup table of pool identifiers for the persistent voters.
    pub persistent_id: BTreeMap<PoolKeyhash, PersistentId>,
    /// Total stake.
    pub total_stake: Coin,
    /// Stake of non-persistent voters.
    pub nonpersistent_stake: CoinFraction,
    /// Committee size.
    pub voters: usize,
}

impl Registry {
    /// Create the registry for the pools `stake` and a committee-size parameter `voters`.
    pub fn make(stake: &[PoolInfo], voters: usize) -> Self {
        let info: BTreeMap<PoolKeyhash, PoolInfo> =
            BTreeMap::from_iter(stake.iter().map(|pool| (pool.reg.pool, pool.clone())));

        let pools: BTreeMap<PoolKeyhash, Coin> =
            BTreeMap::from_iter(stake.iter().map(|pool| (pool.reg.pool, pool.stake)));
        let fa = FaSortition::fait_accompli(&pools, voters);
        let persistent_pool: BTreeMap<PersistentId, PoolKeyhash> = BTreeMap::from_iter(
            (0..fa.persistent.len())
                .zip(fa.persistent)
                .map(|(i, (pool, _))| (PersistentId(i as u16), pool)),
        );
        let persistent_id: BTreeMap<PoolKeyhash, PersistentId> =
            BTreeMap::from_iter(persistent_pool.iter().map(|(k, v)| (*v, k.clone())));

        let total_stake: Coin = stake.iter().map(|pool| pool.stake).sum();

        Registry {
            info,
            persistent_pool,
            persistent_id,
            total_stake,
            nonpersistent_stake: fa.rho,
            voters,
        }
    }
}

impl Arbitrary for Registry {
    fn arbitrary(g: &mut Gen) -> Registry {
        let total = u64::arbitrary(g) % 500000 + 500000;
        let n = usize::arbitrary(g) % 10 + 20;
        let stake = arbitrary_stake_distribution(g, total, n, 5., 1.);
        let pools = arbitrary_pools(g, &stake);
        let voters = realistic_voters(g, stake.len());
        Registry::make(&pools, voters)
    }
}
