use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
};

use anyhow::Result;
use sim_core::config::RawLinkConfig;
use statrs::distribution::{Beta, ContinuousCDF as _};

#[derive(Default)]
pub struct LinkTracker {
    pub connections: BTreeMap<usize, BTreeSet<usize>>,
    pub links: Vec<RawLinkConfig>,
}

impl LinkTracker {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn add(&mut self, from: usize, to: usize, latency: Option<Duration>) {
        if to < from {
            self.add(to, from, latency);
            return;
        }
        self.links.push(RawLinkConfig {
            nodes: (from, to),
            latency_ms: latency.map(|l| l.as_millis() as u64),
        });
        self.connections.entry(from).or_default().insert(to);
        self.connections.entry(to).or_default().insert(from);
    }
}

pub fn distribute_stake(stake_pool_count: usize) -> Result<Vec<u64>> {
    let max_stake = u64::MAX;
    let dist = Beta::new(11.0, 1.0)?;
    let cdf = (0..=stake_pool_count).map(|i| dist.cdf(i as f64 / stake_pool_count as f64));
    Ok(cdf
        .clone()
        .zip(cdf.skip(1))
        .map(|(x1, x2)| {
            let stake_percentage = x2 - x1;
            (max_stake as f64 * stake_percentage) as u64
        })
        .collect())
}
