use std::collections::{BTreeMap, BTreeSet};

use anyhow::{bail, Result};
use clap::Parser;
use rand::{seq::SliceRandom as _, thread_rng, Rng as _};

use crate::strategy::utils::{distance, distribute_stake, GraphBuilder, RawNodeConfig};

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

    let stake = distribute_stake(args.stake_pool_count)?;
    let mut rng = thread_rng();

    let mut graph = GraphBuilder::new();

    println!("generating nodes...");
    for id in 0..args.node_count {
        let stake = stake.get(id).cloned();
        graph.add(RawNodeConfig {
            location: (rng.gen_range(-90.0..90.0), rng.gen_range(0.0..180.0)),
            region: None,
            stake,
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

    use super::{random_graph, RandomGraphArgs};

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
