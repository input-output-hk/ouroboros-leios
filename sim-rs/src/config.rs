use std::{fmt::Display, fs, path::Path};

use anyhow::Result;
use serde::{Deserialize, Serialize};

use crate::probability::FloatDistribution;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PoolId(usize);
impl Display for PoolId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Debug, Deserialize)]
#[serde(untagged)]
enum DistributionConfig {
    Normal { mean: f64, std_dev: f64 },
    ScaledExp { lambda: f64, scale: f64 },
}
impl From<DistributionConfig> for FloatDistribution {
    fn from(value: DistributionConfig) -> Self {
        match value {
            DistributionConfig::Normal { mean, std_dev } => {
                FloatDistribution::normal(mean, std_dev)
            }
            DistributionConfig::ScaledExp { lambda, scale } => {
                FloatDistribution::scaled_exp(lambda, scale)
            }
        }
    }
}

#[derive(Debug, Deserialize)]
struct RawConfig {
    pools: Vec<RawPoolConfig>,
    block_generation_probability: f64,
    max_block_size: u64,
    max_tx_size: u64,
    transaction_frequency_ms: DistributionConfig,
    transaction_size_bytes: DistributionConfig,
}

#[derive(Debug, Deserialize)]
struct RawPoolConfig {
    stake: u64,
}

#[derive(Debug, Clone)]
pub struct SimConfiguration {
    pub pools: Vec<PoolConfiguration>,
    pub block_generation_probability: f64,
    pub max_block_size: u64,
    pub max_tx_size: u64,
    pub transaction_frequency_ms: FloatDistribution,
    pub transaction_size_bytes: FloatDistribution,
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
            block_generation_probability: value.block_generation_probability,
            max_block_size: value.max_block_size,
            max_tx_size: value.max_tx_size,
            transaction_frequency_ms: value.transaction_frequency_ms.into(),
            transaction_size_bytes: value.transaction_size_bytes.into(),
        }
    }
}

pub fn read_config(filename: &Path) -> Result<SimConfiguration> {
    let file = fs::read_to_string(filename)?;
    let raw_config: RawConfig = toml::from_str(&file)?;
    Ok(raw_config.into())
}
