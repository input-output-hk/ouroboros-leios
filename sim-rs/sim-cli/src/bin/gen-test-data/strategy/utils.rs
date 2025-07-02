use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
};

use netsim_core::geo::{latency_between_locations, Location};
use rand::Rng;
use sim_core::config::{RawLinkInfo, RawNode, RawNodeLocation, RawTopology};
use statrs::distribution::{Beta, ContinuousCDF as _};

#[derive(Clone, Debug)]
pub struct RawNodeConfig {
    pub name: String,
    pub location: (f64, f64),
    pub stake: Option<u64>,
    #[expect(unused)]
    pub region: Option<String>,
    pub cores: Option<u64>,
}

#[derive(Clone)]
struct RawLinkConfig {
    pub node: String,
    pub producer: String,
    pub latency_ms: u64,
}

#[derive(Clone, Default)]
pub struct GraphBuilder {
    connections: BTreeMap<usize, BTreeSet<usize>>,
    nodes: Vec<RawNodeConfig>,
    links: Vec<RawLinkConfig>,
}

pub enum Weight {
    Distance,
    Stake,
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
    pub fn bidi_link(&mut self, from: usize, to: usize, latency: Option<Duration>) {
        self.link(from, to, latency);
        self.link(to, from, latency);
    }

    pub fn link(&mut self, node: usize, producer: usize, latency: Option<Duration>) {
        if node == producer {
            return;
        }
        let latency = latency.unwrap_or_else(|| {
            let loc1 = to_netsim_location(self.location_of(node));
            let loc2 = to_netsim_location(self.location_of(producer));
            latency_between_locations(loc1, loc2, 1.)
                .map(|d| d.to_duration())
                .unwrap_or_default()
                .max(Duration::from_millis(1))
        });
        self.links.push(RawLinkConfig {
            node: self.nodes.get(node).unwrap().name.clone(),
            producer: self.nodes.get(producer).unwrap().name.clone(),
            latency_ms: latency.as_millis() as u64,
        });
        self.connections.entry(node).or_default().insert(producer);
    }

    pub fn add_random_connections<R: Rng>(
        &mut self,
        from: usize,
        candidates: impl IntoIterator<Item = usize>,
        target_count: usize,
        weight: Weight,
        rng: &mut R,
        bidi: bool,
    ) {
        let mut candidate_weights = self.candidate_connections(from, candidates, weight);
        let mut total_weight: u128 = candidate_weights.iter().map(|(_, weight)| *weight).sum();
        while self.connections_count(from) < target_count && !candidate_weights.is_empty() {
            let next = rng.random_range(0..total_weight);
            let Some(to_index) = candidate_weights
                .iter()
                .scan(0u128, |cum_weight, (_, weight)| {
                    *cum_weight += weight;
                    Some(*cum_weight)
                })
                .position(|weight| weight >= next)
            else {
                break;
            };
            let (to, to_weight) = candidate_weights.remove(to_index);
            if bidi {
                self.bidi_link(from, to, None);
            } else {
                self.link(from, to, None);
            }
            total_weight -= to_weight;
        }
    }

    fn candidate_connections(
        &self,
        from: usize,
        ids: impl IntoIterator<Item = usize>,
        weight: Weight,
    ) -> Vec<(usize, u128)> {
        let ids = ids
            .into_iter()
            .filter(|c| *c != from && !self.already_connected(from, *c));
        match weight {
            Weight::Distance => {
                let max_distance = distance((-90.0, 90.0), (90.0, 180.0));
                let from_pos = self.location_of(from);
                ids.map(|c| {
                    (
                        c,
                        (max_distance * 10.0 / distance(from_pos, self.location_of(c))) as u128,
                    )
                })
                .collect()
            }
            Weight::Stake => ids
                .map(|c| {
                    let connected_stake: u64 =
                        self.connections(c).flat_map(|p| self.nodes[p].stake).sum();
                    (c, connected_stake as u128)
                })
                .collect(),
        }
    }

    pub fn connections(&self, from: usize) -> impl Iterator<Item = usize> + use<'_> {
        self.connections
            .get(&from)
            .into_iter()
            .flat_map(|set| set.iter())
            .copied()
    }

    pub fn connections_count(&self, from: usize) -> usize {
        self.connections
            .get(&from)
            .map(|c| c.len())
            .unwrap_or_default()
    }

    pub fn already_connected(&self, from: usize, to: usize) -> bool {
        self.connections
            .get(&from)
            .map(|c| c.contains(&to))
            .unwrap_or_default()
    }

    pub fn into_topology(self) -> RawTopology {
        let mut nodes: BTreeMap<_, _> = self
            .nodes
            .into_iter()
            .map(|n| {
                let name = n.name;
                let node = RawNode {
                    stake: n.stake,
                    location: RawNodeLocation::Coords(n.location),
                    cpu_core_count: n.cores,
                    tx_conflict_fraction: None,
                    tx_generation_weight: None,
                    producers: BTreeMap::new(),
                    adversarial: None,
                    behaviours: vec![],
                };
                (name, node)
            })
            .collect();
        for link in self.links {
            nodes.get_mut(&link.node).unwrap().producers.insert(
                link.producer,
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

pub fn distribute_stake(stake_pool_count: usize) -> Vec<u64> {
    let max_stake = u64::MAX;
    let dist = Beta::new(11.0, 1.0).unwrap();
    let cdf = (0..=stake_pool_count).map(|i| dist.cdf(i as f64 / stake_pool_count as f64));
    cdf.clone()
        .zip(cdf.skip(1))
        .map(|(x1, x2)| {
            let stake_percentage = x2 - x1;
            (max_stake as f64 * stake_percentage) as u64
        })
        .collect()
}

fn distance((lat1, long1): (f64, f64), (lat2, long2): (f64, f64)) -> f64 {
    // euclidean distance probably good enough
    let dist_lat = (lat2 - lat1).abs();
    let dist_long = (long2 - long1).abs().min((long2 - long1 + 180.0).abs());
    (dist_lat.powi(2) + dist_long.powi(2)).sqrt()
}
