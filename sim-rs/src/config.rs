use std::{fmt::Display, fs, path::Path};

use anyhow::Result;
use serde::Deserialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PoolId(usize);
impl Display for PoolId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Debug, Deserialize)]
struct RawConfig {
    pools: Vec<RawPoolConfig>,
    vrf_max_score: u64,
}

#[derive(Debug, Deserialize)]
struct RawPoolConfig {
    stake: u64,
}

#[derive(Debug, Clone)]
pub struct SimConfiguration {
    pub pools: Vec<PoolConfiguration>,
    pub vrf_max_score: u64,
}

#[derive(Debug, Clone)]
pub struct PoolConfiguration {
    pub id: PoolId,
    pub stake: u64,
}

impl From<RawConfig> for SimConfiguration {
    fn from(value: RawConfig) -> Self {
        let pools = value
            .pools
            .into_iter()
            .enumerate()
            .map(|(index, raw)| PoolConfiguration {
                id: PoolId(index),
                stake: raw.stake,
            })
            .collect();
        Self {
            pools,
            vrf_max_score: value.vrf_max_score,
        }
    }
}

pub fn read_config(filename: &Path) -> Result<SimConfiguration> {
    let file = fs::read_to_string(filename)?;
    let raw_config: RawConfig = toml::from_str(&file)?;
    Ok(raw_config.into())
}
