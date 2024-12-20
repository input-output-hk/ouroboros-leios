use std::collections::{BTreeMap, BTreeSet};

use anyhow::{bail, Result};
use clap::Parser;
use rand::{seq::SliceRandom as _, thread_rng, Rng as _};
use sim_core::config::{RawConfig, RawNodeConfig};

use crate::strategy::utils::{distance, distribute_stake, generate_full_config, LinkTracker};

#[derive(Debug, Parser)]
pub struct RandomGraphArgs {
    node_count: usize,
    stake_pool_count: usize,
}

pub fn random_graph(args: &RandomGraphArgs) -> Result<RawConfig> {
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
            region: None,
            stake,
        });
    }

    println!("generating edges...");
    let alpha = 0.15;
    let beta = 0.25 * (100.0 / args.node_count as f64).min(1.0);
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

    use super::{random_graph, RandomGraphArgs};

    #[test]
    fn should_generate_valid_graph() {
        let args = RandomGraphArgs {
            node_count: 1000,
            stake_pool_count: 50,
        };

        let raw_config = random_graph(&args).unwrap();
        let config: SimConfiguration = raw_config.into();
        config.validate().unwrap();
    }
}
