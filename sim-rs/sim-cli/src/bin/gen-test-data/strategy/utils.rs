use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    time::Duration,
};

use anyhow::Result;
use sim_core::config::{DistributionConfig, RawConfig, RawLinkConfig, RawNodeConfig};
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

pub fn distance((lat1, long1): (f64, f64), (lat2, long2): (f64, f64)) -> f64 {
    // euclidean distance probably good enough
    let dist_x = (lat2 - lat1).rem_euclid(180.0);
    let dist_y = (long2 - long1).rem_euclid(180.0);
    (dist_x.powi(2) + dist_y.powi(2)).sqrt()
}

pub fn generate_full_config(nodes: Vec<RawNodeConfig>, links: Vec<RawLinkConfig>) -> RawConfig {
    let vote_probability = 500.0;
    let vote_threshold = 150;

    RawConfig {
        seed: None,
        timescale: None,
        slots: None,
        nodes,
        trace_nodes: HashSet::new(),
        links,
        block_generation_probability: 0.05,
        ib_generation_probability: 5.0,
        eb_generation_probability: 5.0,
        vote_probability,
        vote_threshold,
        ib_shards: 8,
        max_block_size: 90112,
        stage_length: 2,
        deliver_stage_count: 2,
        uniform_ib_generation: true,
        max_ib_requests_per_peer: 1,
        one_vote_per_vrf: true,
        max_ib_size: 327680,
        max_tx_size: 16384,
        transaction_frequency_ms: DistributionConfig::Exp {
            lambda: 0.85,
            scale: Some(1000.0),
        },
        transaction_size_bytes: DistributionConfig::LogNormal {
            mu: 6.833,
            sigma: 1.127,
        },
    }
}
