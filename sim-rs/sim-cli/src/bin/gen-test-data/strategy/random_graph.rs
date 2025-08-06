use std::collections::BTreeSet;

use anyhow::{Result, bail};
use clap::Parser;
use rand::{Rng as _, seq::IndexedRandom as _};

use crate::strategy::utils::{GraphBuilder, RawNodeConfig, Weight, distribute_stake};

#[derive(Debug, Parser)]
pub struct RandomGraphArgs {
    node_count: usize,
    stake_pool_count: usize,
    min_connections: usize,
    max_connections: usize,
}

pub fn random_graph(args: &RandomGraphArgs) -> Result<GraphBuilder> {
    if args.stake_pool_count >= args.node_count {
        bail!("At least one node must not be a stake pool");
    }

    let stake = distribute_stake(args.stake_pool_count);
    let mut rng = rand::rng();

    let mut graph = GraphBuilder::new();

    println!("generating nodes...");
    for id in 0..args.node_count {
        let stake = stake.get(id).cloned();
        graph.add(RawNodeConfig {
            name: format!("node-{id}"),
            location: (rng.random_range(-90.0..90.0), rng.random_range(0.0..180.0)),
            region: None,
            stake,
            cores: None,
        });
    }

    println!("generating edges...");
    for from in 0..args.node_count {
        // stake pools don't connect directly to each other
        let first_candidate_connection = if from < args.stake_pool_count {
            args.stake_pool_count
        } else {
            from + 1
        };

        let candidates = first_candidate_connection..args.node_count;
        let target_count = rng.random_range(args.min_connections..args.max_connections);
        graph.add_random_connections(
            from,
            candidates,
            target_count,
            Weight::Distance,
            &mut rng,
            true,
        );
    }

    // Every node must connect to at least one other node
    for from in 0..args.node_count {
        if graph.connections_count(from) == 0 {
            let candidate_targets: Vec<usize> = if from < args.stake_pool_count {
                (args.stake_pool_count..args.node_count).collect()
            } else {
                (0..args.node_count).filter(|&to| to != from).collect()
            };
            let to = candidate_targets.choose(&mut rng).cloned().unwrap();
            graph.bidi_link(from, to, None);
        }
    }

    // Make sure the relays are fully connected
    let mut connected_nodes = BTreeSet::new();
    track_connections(&mut connected_nodes, &graph, args.stake_pool_count);

    let mut last_conn = args.stake_pool_count;
    for relay in (args.stake_pool_count + 1)..args.node_count {
        if !connected_nodes.contains(&relay) {
            let from = last_conn;
            let to = relay;
            graph.bidi_link(from, to, None);
            track_connections(&mut connected_nodes, &graph, relay);
            last_conn = relay;
        }
    }

    Ok(graph)
}

fn track_connections(connected: &mut BTreeSet<usize>, graph: &GraphBuilder, from: usize) {
    if connected.insert(from) {
        for next in graph.connections(from) {
            track_connections(connected, graph, next);
        }
    }
}

#[cfg(test)]
mod tests {
    use sim_core::config::Topology;

    use super::{RandomGraphArgs, random_graph};

    #[test]
    fn should_generate_valid_graph() {
        let args = RandomGraphArgs {
            node_count: 1000,
            stake_pool_count: 50,
            min_connections: 5,
            max_connections: 15,
        };

        let raw = random_graph(&args).unwrap();
        let topology: Topology = raw.into_topology().into();
        topology.validate().unwrap();
    }
}
