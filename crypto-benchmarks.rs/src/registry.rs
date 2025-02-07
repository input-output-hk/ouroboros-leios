use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

use crate::key::Reg;
use crate::primitive::{arbitrary_coin, Coin, PoolKeyhash};

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug, Serialize, Deserialize)]
pub struct PersistentId(pub u16);

impl Arbitrary for PersistentId {
    fn arbitrary(g: &mut Gen) -> Self {
        PersistentId(u16::arbitrary(g))
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize, Deserialize)]
pub struct PoolInfo {
    pub reg: Reg,
    pub stake: Coin,
}

impl Arbitrary for PoolInfo {
    fn arbitrary(g: &mut Gen) -> Self {
        PoolInfo {
            reg: Reg::arbitrary(g),
            stake: arbitrary_coin(g),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize, Deserialize)]
pub struct Registry {
    pub info: BTreeMap<PoolKeyhash, PoolInfo>,
    pub persistent: BTreeMap<PersistentId, PoolKeyhash>,
    pub total_stake: Coin,
}
