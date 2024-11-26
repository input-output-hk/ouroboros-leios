use std::collections::{BTreeMap, BTreeSet};

use anyhow::{bail, Result};
use clap::Parser;
use rand::{seq::SliceRandom as _, thread_rng, Rng as _};
use sim_core::config::{RawLinkConfig, RawNodeConfig};

use crate::strategy::utils::{distribute_stake, LinkTracker};

#[derive(Debug, Parser)]
pub struct RandomGraphArgs {
    node_count: usize,
    stake_pool_count: usize,
}

fn distance((lat1, long1): (f64, f64), (lat2, long2): (f64, f64)) -> f64 {
    // euclidean distance probably good enough
    let dist_x = (lat2 - lat1).rem_euclid(180.0);
    let dist_y = (long2 - long1).rem_euclid(180.0);
    (dist_x.powi(2) + dist_y.powi(2)).sqrt()
}

pub fn random_graph(args: &RandomGraphArgs) -> Result<(Vec<RawNodeConfig>, Vec<RawLinkConfig>)> {
    if args.stake_pool_count >= args.node_count {
        bail!("At least one node must not be a stake pool");
    }

    let stake = distribute_stake(args.stake_pool_count)?;
    let mut rng = thread_rng();

    let mut nodes = vec![];
    let mut links = LinkTracker::new();

    println!("generating nodes...");
    for id in 0..args.node_count {
        let stake = stake.get(id).cloned();
        nodes.push(RawNodeConfig {
            location: (rng.gen_range(-90.0..90.0), rng.gen_range(0.0..180.0)),
            stake,
        });
    }

    println!("generating edges...");
    let alpha = 0.15;
    let beta = 0.2;
    let max_distance = distance((0.0, 90.0), (90.0, 180.0));
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
                (0..args.node_count).filter(|&to| to == from).collect()
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

    Ok((nodes, links.links))
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
