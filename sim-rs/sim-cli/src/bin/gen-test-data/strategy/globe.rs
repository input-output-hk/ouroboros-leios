use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::PathBuf,
};

use anyhow::{bail, Result};
use clap::Parser;
use rand::{seq::SliceRandom as _, thread_rng, Rng as _};
use serde::Deserialize;
use sim_core::config::RawNodeConfig;

use crate::strategy::utils::{distance, distribute_stake, GraphBuilder};

#[derive(Debug, Parser)]
pub struct GlobeArgs {
    node_count: usize,
    stake_pool_count: usize,
    min_connections: usize,
    max_connections: usize,
    distribution: PathBuf,
}

#[derive(Debug, Deserialize)]
struct Distribution {
    countries: Vec<Country>,
}

#[derive(Debug, Deserialize)]
struct Country {
    name: String,
    regions: Vec<RegionData>,
}

#[derive(Debug, Deserialize)]
struct RegionData {
    id: u64,
    latitude: f64,
    longitude: f64,
    proportion: u64,
}

#[derive(Clone)]
struct Region {
    name: String,
    location: (f64, f64),
}

fn distribute_regions(node_count: usize, distribution: Distribution) -> Vec<Region> {
    let mut region_pool = vec![];
    for country in distribution.countries {
        for region in country.regions {
            for _ in 0..region.proportion {
                let id = region.id;
                let location = (region.latitude, (region.longitude + 180.0) / 2.0);
                region_pool.push((country.name.clone(), id, location));
            }
        }
    }

    let mut country_regions: HashMap<String, Vec<u64>> = HashMap::new();
    let mut results = vec![];
    let mut rng = thread_rng();
    for _ in 0..node_count {
        let (country, id, location) = region_pool
            .get(rng.gen_range(0..region_pool.len()))
            .unwrap();
        let regions = country_regions.entry(country.clone()).or_default();
        let number = match regions.iter().position(|r| r == id) {
            Some(index) => index + 1,
            None => {
                regions.push(*id);
                regions.len()
            }
        };
        results.push(Region {
            name: format!("{country} {number}"),
            location: *location,
        });
    }

    results
}

pub fn globe(args: &GlobeArgs) -> Result<GraphBuilder> {
    if args.stake_pool_count >= args.node_count {
        bail!("At least one node must not be a stake pool");
    }

    let distribution: Distribution = toml::from_str(&std::fs::read_to_string(&args.distribution)?)?;
    let regions = distribute_regions(args.node_count, distribution);

    let stake = distribute_stake(args.stake_pool_count)?;
    let mut rng = thread_rng();

    let mut graph = GraphBuilder::new();

    println!("generating nodes...");
    for (id, region) in regions.into_iter().enumerate() {
        let location = (
            (region.location.0 + rng.gen_range(-4.0..4.0)).clamp(-90.0, 90.0),
            (region.location.1 + rng.gen_range(-4.0..4.0)).clamp(0.0, 180.0),
        );
        let stake = stake.get(id).cloned();
        graph.add(RawNodeConfig {
            location,
            region: Some(region.name),
            stake,
            cpu_multiplier: 1.0,
            cores: None,
        });
    }

    println!("generating edges...");
    let max_distance = distance((-90.0, 90.0), (90.0, 180.0));
    for from in 0..args.node_count {
        // stake pools don't connect directly to each other
        let first_candidate_connection = if from < args.stake_pool_count {
            args.stake_pool_count
        } else {
            from + 1
        };

        let mut candidates: Vec<_> = (first_candidate_connection..args.node_count)
            .filter(|c| *c != from && !graph.exists(from, *c))
            .map(|c| {
                (
                    c,
                    (max_distance / distance(graph.location_of(from), graph.location_of(c))) as u64,
                )
            })
            .collect();
        let mut total_weight: u64 = candidates.iter().map(|(_, weight)| *weight).sum();
        let conn_count = rng.gen_range(args.min_connections..args.max_connections);
        while graph.count(from) < conn_count && !candidates.is_empty() {
            let next = rng.gen_range(0..total_weight);
            let Some(to_index) = candidates
                .iter()
                .scan(0u64, |cum_weight, (_, weight)| {
                    *cum_weight += weight;
                    Some(*cum_weight)
                })
                .position(|weight| weight >= next)
            else {
                break;
            };
            let (to, to_weight) = candidates.remove(to_index);
            graph.link(from, to, None);
            total_weight -= to_weight;
        }
    }

    // Every node must connect to at least one other node
    for from in 0..args.node_count {
        if !graph.connections.contains_key(&from) {
            let candidate_targets: Vec<usize> = if from < args.stake_pool_count {
                (args.stake_pool_count..args.node_count).collect()
            } else {
                (0..args.node_count).filter(|&to| to != from).collect()
            };
            let to = candidate_targets.choose(&mut rng).cloned().unwrap();
            graph.link(from, to, None);
        }
    }

    // Make sure the relays are fully connected
    let mut connected_nodes = BTreeSet::new();
    track_connections(
        &mut connected_nodes,
        &graph.connections,
        args.stake_pool_count,
    );

    let mut last_conn = args.stake_pool_count;
    for relay in (args.stake_pool_count + 1)..args.node_count {
        if !connected_nodes.contains(&relay) {
            let from = last_conn;
            let to = relay;
            graph.link(from, to, None);
            track_connections(&mut connected_nodes, &graph.connections, relay);
            last_conn = relay;
        }
    }

    Ok(graph)
}

fn track_connections(
    connected: &mut BTreeSet<usize>,
    connections: &BTreeMap<usize, BTreeSet<usize>>,
    from: usize,
) {
    if connected.insert(from) {
        let Some(nexts) = connections.get(&from) else {
            return;
        };
        for next in nexts {
            track_connections(connected, connections, *next);
        }
    }
}

#[cfg(test)]
mod tests {
    use sim_core::config::Topology;

    use super::{globe, GlobeArgs};

    #[test]
    fn should_generate_valid_graph() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/test_data/distribution.toml");
        let args = GlobeArgs {
            node_count: 1000,
            stake_pool_count: 50,
            min_connections: 5,
            max_connections: 15,
            distribution: path.into(),
        };

        let raw = globe(&args).unwrap();
        let topology: Topology = raw.into_topology().into();
        topology.validate().unwrap();
    }
}
