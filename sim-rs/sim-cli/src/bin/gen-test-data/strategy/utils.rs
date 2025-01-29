use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
};

use anyhow::Result;
use netsim_core::geo::{latency_between_locations, Location};
use sim_core::config::{
    RawLegacyTopology, RawLinkConfig, RawLinkInfo, RawNode, RawNodeConfig, RawNodeLocation,
    RawTopology,
};
use statrs::distribution::{Beta, ContinuousCDF as _};

#[derive(Clone, Default)]
pub struct GraphBuilder {
    pub connections: BTreeMap<usize, BTreeSet<usize>>,
    nodes: Vec<RawNodeConfig>,
    links: Vec<RawLinkConfig>,
}

impl GraphBuilder {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn add(&mut self, node: RawNodeConfig) -> usize {
        let id = self.nodes.len();
        self.nodes.push(node);
        id
    }
    pub fn location_of(&self, id: usize) -> (f64, f64) {
        self.nodes[id].location
    }
    pub fn link(&mut self, from: usize, to: usize, latency: Option<Duration>) {
        if to < from {
            self.link(to, from, latency);
            return;
        }
        let latency = latency.unwrap_or_else(|| {
            let loc1 = to_netsim_location(self.location_of(from));
            let loc2 = to_netsim_location(self.location_of(to));
            latency_between_locations(loc1, loc2, 1.)
                .unwrap()
                .to_duration()
        });
        self.links.push(RawLinkConfig {
            nodes: (from, to),
            latency_ms: latency.as_millis() as u64,
        });
        self.connections.entry(from).or_default().insert(to);
        self.connections.entry(to).or_default().insert(from);
    }
    pub fn count(&self, from: usize) -> usize {
        self.connections
            .get(&from)
            .map(|c| c.len())
            .unwrap_or_default()
    }
    pub fn exists(&self, from: usize, to: usize) -> bool {
        self.connections
            .get(&from)
            .map(|c| c.contains(&to))
            .unwrap_or_default()
    }

    pub fn into_legacy_topology(self) -> RawLegacyTopology {
        RawLegacyTopology {
            nodes: self.nodes,
            links: self.links,
        }
    }

    pub fn into_topology(self) -> RawTopology {
        let mut nodes: BTreeMap<_, _> = self
            .nodes
            .into_iter()
            .enumerate()
            .map(|(id, n)| {
                let name = format!("node-{id}");
                let node = RawNode {
                    stake: n.stake,
                    location: RawNodeLocation::Coords(n.location),
                    cpu_core_count: n.cores,
                    producers: BTreeMap::new(),
                };
                (name, node)
            })
            .collect();
        for link in self.links {
            let from_id = format!("node-{}", link.nodes.0);
            let to_id = format!("node-{}", link.nodes.1);
            nodes.get_mut(&from_id).unwrap().producers.insert(
                to_id.clone(),
                RawLinkInfo {
                    latency_ms: link.latency_ms as f64,
                    bandwidth_bytes_per_second: None,
                },
            );
            nodes.get_mut(&to_id).unwrap().producers.insert(
                from_id,
                RawLinkInfo {
                    latency_ms: link.latency_ms as f64,
                    bandwidth_bytes_per_second: None,
                },
            );
        }
        RawTopology { nodes }
    }
}

fn to_netsim_location((lat, long): (f64, f64)) -> Location {
    ((lat * 10000.) as i64, (long * 10000.) as u64)
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
    let dist_lat = (lat2 - lat1).abs();
    let dist_long = (long2 - long1).abs().min((long2 - long1 + 180.0).abs());
    (dist_lat.powi(2) + dist_long.powi(2)).sqrt()
}
