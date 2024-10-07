use std::{fmt::Display, fs, path::Path, time::Duration};

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
impl PoolId {
    pub fn to_inner(self) -> usize {
        self.0
    }
    pub fn from_usize(value: usize) -> Self {
        Self(value)
    }
}

#[derive(Debug, Deserialize)]
#[serde(untagged)]
enum DistributionConfig {
    Normal { mean: f64, std_dev: f64 },
    Exp { lambda: f64, scale: Option<f64> },
    LogNormal { mu: f64, sigma: f64 },
}
impl From<DistributionConfig> for FloatDistribution {
    fn from(value: DistributionConfig) -> Self {
        match value {
            DistributionConfig::Normal { mean, std_dev } => {
                FloatDistribution::normal(mean, std_dev)
            }
            DistributionConfig::Exp { lambda, scale } => {
                FloatDistribution::scaled_exp(lambda, scale.unwrap_or(1.))
            }
            DistributionConfig::LogNormal { mu, sigma } => {
                FloatDistribution::log_normal(mu, sigma)
            }
        }
    }
}

#[derive(Debug, Deserialize)]
struct RawConfig {
    pools: Vec<RawPoolConfig>,
    links: Vec<RawLinkConfig>,
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

#[derive(Debug, Deserialize)]
struct RawLinkConfig {
    pools: [usize; 2],
    latency_ms: u64,
}

#[derive(Debug, Clone)]
pub struct SimConfiguration {
    pub pools: Vec<PoolConfiguration>,
    pub links: Vec<LinkConfiguration>,
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
    pub peers: Vec<PoolId>,
}

#[derive(Debug, Clone)]
pub struct LinkConfiguration {
    pub pools: [PoolId; 2],
    pub latency: Duration,
}

impl From<RawConfig> for SimConfiguration {
    fn from(value: RawConfig) -> Self {
        let mut pools: Vec<PoolConfiguration> = value
            .pools
            .into_iter()
            .enumerate()
            .map(|(index, raw)| PoolConfiguration {
                id: PoolId(index),
                stake: raw.stake,
                peers: vec![],
            })
            .collect();
        let mut links = vec![];
        for link in value.links {
            let [id1, id2] = link.pools;
            pools[id1].peers.push(PoolId(id2));
            pools[id2].peers.push(PoolId(id1));
            links.push(LinkConfiguration {
                pools: [PoolId(id1), PoolId(id2)],
                latency: Duration::from_millis(link.latency_ms),
            });
        }
        Self {
            pools,
            links,
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
