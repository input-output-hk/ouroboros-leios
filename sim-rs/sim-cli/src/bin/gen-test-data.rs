use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    fs,
    path::PathBuf,
};

use anyhow::Result;
use clap::Parser;
use rand::{seq::SliceRandom, thread_rng, Rng};
use sim_core::config::{DistributionConfig, RawConfig, RawLinkConfig, RawNodeConfig};

#[derive(Debug, Parser)]
struct Args {
    path: PathBuf,
    node_count: usize,
    stake_pool_count: usize,
}

fn distance((lat1, long1): (f64, f64), (lat2, long2): (f64, f64)) -> f64 {
    // euclidean distance probably good enough
    let dist_x = (lat2 - lat1).rem_euclid(180.0);
    let dist_y = (long2 - long1).rem_euclid(180.0);
    (dist_x.powi(2) + dist_y.powi(2)).sqrt()
}

fn main() -> Result<()> {
    let args = Args::parse();
    assert!(args.stake_pool_count < args.node_count);

    let mut rng = thread_rng();

    let mut nodes = vec![];
    let mut links = vec![];

    println!("generating nodes...");
    for id in 0..args.node_count {
        let stake = if id < args.stake_pool_count {
            Some(rng.gen_range(100..100000))
        } else {
            None
        };
        nodes.push(RawNodeConfig {
            location: (rng.gen_range(-90.0..90.0), rng.gen_range(0.0..180.0)),
            stake,
        });
    }

    println!("generating edges...");
    let alpha = 0.15;
    let beta = 0.2;
    let max_distance = distance((0.0, 90.0), (90.0, 180.0));
    let mut connections: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for from in 0..args.node_count {
        // stake pools don't connect directly to each other
        let first_candidate_connection = if from < args.stake_pool_count {
            args.stake_pool_count
        } else {
            from + 1
        };

        for to in first_candidate_connection..args.node_count {
            // nodes are connected probabilistically, based on how far apart they are
            let dist = distance(nodes[from].location, nodes[to].location);
            let probability = alpha * (-dist / (beta * max_distance)).exp();
            if rng.gen_bool(probability) {
                links.push(RawLinkConfig {
                    nodes: (from, to),
                    latency_ms: None,
                });
                connections.entry(from).or_default().insert(to);
                connections.entry(to).or_default().insert(from);
            }
        }
    }

    // Every node must connect to at least one other node
    for from in 0..args.node_count {
        if !connections.contains_key(&from) {
            let candidate_targets: Vec<usize> = if from < args.stake_pool_count {
                (args.stake_pool_count..args.node_count).collect()
            } else {
                (0..args.node_count).filter(|&to| to == from).collect()
            };
            let to = candidate_targets.choose(&mut rng).cloned().unwrap();
            links.push(RawLinkConfig {
                nodes: (from, to),
                latency_ms: None,
            });
            connections.entry(from).or_default().insert(to);
            connections.entry(to).or_default().insert(from);
        }
    }

    // Make sure the relays are fully connected
    let mut connected_nodes = BTreeSet::new();
    track_connections(&mut connected_nodes, &connections, args.stake_pool_count);

    let mut last_conn = args.stake_pool_count;
    for relay in (args.stake_pool_count + 1)..args.node_count {
        if !connected_nodes.contains(&relay) {
            let from = last_conn;
            let to = relay;
            links.push(RawLinkConfig {
                nodes: (from, to),
                latency_ms: None,
            });
            connections.entry(from).or_default().insert(to);
            connections.entry(to).or_default().insert(from);
            track_connections(&mut connected_nodes, &connections, relay);
            last_conn = relay;
        }
    }

    let data = RawConfig {
        seed: None,
        timescale: None,
        slots: None,
        nodes,
        trace_nodes: HashSet::new(),
        links,
        block_generation_probability: 0.05,
        ib_generation_probability: 5.0,
        ib_shards: 8,
        max_block_size: 90112,
        max_ib_requests_per_peer: 1,
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
    };

    fs::write(args.path, toml::to_string_pretty(&data)?)?;

    Ok(())
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
