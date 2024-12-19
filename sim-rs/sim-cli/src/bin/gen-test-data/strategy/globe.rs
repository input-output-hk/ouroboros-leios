use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::PathBuf,
};

use anyhow::{bail, Result};
use clap::Parser;
use rand::{seq::SliceRandom as _, thread_rng, Rng as _};
use serde::Deserialize;
use sim_core::config::{RawConfig, RawNodeConfig};

use crate::strategy::utils::{distance, distribute_stake, generate_full_config, LinkTracker};

#[derive(Debug, Parser)]
pub struct GlobeArgs {
    node_count: usize,
    stake_pool_count: usize,
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

pub fn globe(args: &GlobeArgs) -> Result<RawConfig> {
    if args.stake_pool_count >= args.node_count {
        bail!("At least one node must not be a stake pool");
    }

    let distribution: Distribution = toml::from_str(&std::fs::read_to_string(&args.distribution)?)?;
    let regions = distribute_regions(args.node_count, distribution);

    let stake = distribute_stake(args.stake_pool_count)?;
    let mut rng = thread_rng();

    let mut nodes = vec![];
    let mut links = LinkTracker::new();

    println!("generating nodes...");
    for (id, region) in regions.into_iter().enumerate() {
        let location = (
            (region.location.0 + rng.gen_range(-4.0..4.0)).clamp(-90.0, 90.0),
            (region.location.1 + rng.gen_range(-4.0..4.0)).clamp(0.0, 180.0),
        );
        let stake = stake.get(id).cloned();
        nodes.push(RawNodeConfig {
            location,
            region: Some(region.name),
            stake,
        });
    }

    println!("generating edges...");
    let alpha = 0.05;
    let beta = 0.2 * (500.0 / args.node_count as f64).min(1.0);
    let max_distance = distance((-90.0, 90.0), (90.0, 180.0));
    for from in 0..args.node_count {
        // stake pools don't connect directly to each other
        let first_candidate_connection = if from < args.stake_pool_count {
            args.stake_pool_count
        } else {
            from + 1
        };

        for to in first_candidate_connection..args.node_count {
            if from == to {
                continue;
            }
            // nodes are connected probabilistically, based on how far apart they are
            let dist = distance(nodes[from].location, nodes[to].location);
            let probability = beta * (-dist / (alpha * max_distance)).exp();
            if rng.gen_bool(probability) {
                links.add(from, to, None);
            }
        }
    }

    // Every node must connect to at least one other node
    for from in 0..args.node_count {
        if !links.connections.contains_key(&from) {
            let candidate_targets: Vec<usize> = if from < args.stake_pool_count {
                (args.stake_pool_count..args.node_count).collect()
            } else {
                (0..args.node_count).filter(|&to| to != from).collect()
            };
            let to = candidate_targets.choose(&mut rng).cloned().unwrap();
            links.add(from, to, None);
        }
    }

    // Make sure the relays are fully connected
    let mut connected_nodes = BTreeSet::new();
    track_connections(
        &mut connected_nodes,
        &links.connections,
        args.stake_pool_count,
    );

    let mut last_conn = args.stake_pool_count;
    for relay in (args.stake_pool_count + 1)..args.node_count {
        if !connected_nodes.contains(&relay) {
            let from = last_conn;
            let to = relay;
            links.add(from, to, None);
            track_connections(&mut connected_nodes, &links.connections, relay);
            last_conn = relay;
        }
    }

    Ok(generate_full_config(nodes, links.links))
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
    use sim_core::config::SimConfiguration;

    use super::{globe, GlobeArgs};

    #[test]
    fn should_generate_valid_graph() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/test_data/distribution.toml");
        let args = GlobeArgs {
            node_count: 1000,
            stake_pool_count: 50,
            distribution: path.into(),
        };

        let raw_config = globe(&args).unwrap();
        let config: SimConfiguration = raw_config.into();
        config.validate().unwrap();
    }
}
