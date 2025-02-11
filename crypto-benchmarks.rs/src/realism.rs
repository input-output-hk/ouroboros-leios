use quickcheck::{Arbitrary, Gen};

use crate::primitive::Coin;

pub fn realistic_pool_count(g: &mut Gen) -> usize {
    usize::arbitrary(g) % 1500 + 1500
}

pub fn realistic_total_stake(g: &mut Gen) -> Coin {
    u64::arbitrary(g) % 30000000000000000 + 15000000000000000
}

pub fn realistic_voters(g: &mut Gen, pools: usize) -> usize {
    pools * (usize::arbitrary(g) % 500 + 500) / 1000
}
