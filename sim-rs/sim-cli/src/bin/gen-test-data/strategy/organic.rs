use std::time::Duration;

use anyhow::{bail, Result};
use clap::Parser;
use rand::{seq::SliceRandom, Rng};

use crate::strategy::utils::GraphBuilder;

use super::utils::{distribute_stake, RawNodeConfig, Weight};

#[derive(Debug, Parser)]
pub struct OrganicArgs {
    node_count: usize,
    stake_pool_count: usize,
    outgoing_connections: usize,
    #[clap(default_value_t = 0.05)]
    cluster_probability: f64,
}

struct Cluster {
    location: (f64, f64),
    pool_ids: Vec<usize>,
    relay_ids: Vec<usize>,
}

pub fn organic(args: &OrganicArgs) -> Result<GraphBuilder> {
    if args.stake_pool_count >= args.node_count {
        bail!("At least one node must not be a stake pool");
    }
    let relay_count = args.node_count - args.stake_pool_count;

    let stakes = distribute_stake(args.stake_pool_count);
    let mut rng = rand::rng();

    let mut graph = GraphBuilder::new();

    // Randomly form clusters of pools.
    // Each cluster represents one stake pool operator and their pools.
    let mut clusters: Vec<Cluster> = vec![];
    for index in 0..args.stake_pool_count {
        let create_new_cluster = clusters.is_empty()
            || (clusters.len() < relay_count && !rng.random_bool(args.cluster_probability));
        let cluster = if create_new_cluster {
            clusters.push(Cluster {
                location: (rng.random_range(-90.0..90.0), rng.random_range(0.0..180.0)),
                pool_ids: vec![],
                relay_ids: vec![],
            });
            clusters.last_mut().unwrap()
        } else {
            let cluster_index = rng.random_range(0..clusters.len());
            clusters.get_mut(cluster_index).unwrap()
        };
        let id = graph.add(RawNodeConfig {
            name: format!("pool-{index}"),
            location: nearby(&mut rng, cluster.location, 0.5),
            stake: stakes.get(index).copied(),
            region: None,
            cores: None,
        });
        cluster.pool_ids.push(id);
    }

    // Every cluster needs at least one relay node.
    for (index, cluster) in clusters.iter_mut().enumerate() {
        let id = graph.add(RawNodeConfig {
            name: format!("relay-{}", args.stake_pool_count + index),
            location: nearby(&mut rng, cluster.location, 1.0),
            stake: None,
            region: None,
            cores: None,
        });
        cluster.relay_ids.push(id);
    }

    // Assign any leftover relay nodes randomly.
    for index in (args.stake_pool_count + clusters.len())..args.node_count {
        let cluster_index = rng.random_range(0..clusters.len());
        let cluster = &mut clusters[cluster_index];
        let id = graph.add(RawNodeConfig {
            name: format!("relay-{index}"),
            location: nearby(&mut rng, cluster.location, 1.0),
            stake: None,
            region: None,
            cores: None,
        });
        clusters[cluster_index].relay_ids.push(id);
    }

    // Within a cluster, all pools should connect to all relays,
    // and all relays should connect to all other relays.
    for cluster in &clusters {
        for relay in &cluster.relay_ids {
            for pool in &cluster.pool_ids {
                graph.bidi_link(*relay, *pool, Some(Duration::from_millis(1)));
            }
            for other_relay in &cluster.relay_ids {
                graph.link(*relay, *other_relay, Some(Duration::from_millis(1)));
            }
        }
    }

    // Every cluster needs at least one relay with an incoming connection from a relay in another cluster.
    // Build a daisy chain of relays so that we guarantee a strongly connected graph.
    let mut cluster_ids: Vec<usize> = (0..clusters.len()).collect();
    cluster_ids.shuffle(&mut rng);
    let from_clusters = cluster_ids.iter().copied();
    let to_clusters = cluster_ids
        .iter()
        .copied()
        .skip(1)
        .chain(cluster_ids.first().copied());
    for (cluster_id, producer_cluster_id) in from_clusters.zip(to_clusters) {
        let from_relays = &clusters[cluster_id].relay_ids;
        let node = from_relays[rng.random_range(0..from_relays.len())];

        let to_relays = &clusters[producer_cluster_id].relay_ids;
        let producer = to_relays[rng.random_range(0..to_relays.len())];

        graph.link(node, producer, None);
    }

    // Now give every relay as many outgoing connections as we are configured to.
    for relay_id in args.stake_pool_count..args.node_count {
        // half a relay's connections should be (relatively) nearby
        graph.add_random_connections(
            relay_id,
            args.stake_pool_count..args.node_count,
            args.outgoing_connections / 2,
            Weight::Distance,
            &mut rng,
            false,
        );
        // the other half should be weighted by stake
        graph.add_random_connections(
            relay_id,
            args.stake_pool_count..args.node_count,
            args.outgoing_connections,
            Weight::Stake,
            &mut rng,
            false,
        );
    }

    Ok(graph)
}

fn nearby<R: Rng>(rng: &mut R, location: (f64, f64), dist: f64) -> (f64, f64) {
    let min_lat = (location.0 - dist).max(-90.0);
    let max_lat = (location.0 + dist).min(90.0);
    let min_long = (location.1 - dist).max(0.0);
    let max_long = (location.1 + dist).min(180.0);
    (
        rng.random_range(min_lat..max_lat),
        rng.random_range(min_long..max_long),
    )
}

#[cfg(test)]
mod tests {
    use sim_core::config::Topology;

    use super::{organic, OrganicArgs};

    #[test]
    fn should_generate_valid_graph() {
        let args = OrganicArgs {
            node_count: 75,
            stake_pool_count: 50,
            outgoing_connections: 20,
            cluster_probability: 0.05,
        };

        let raw = organic(&args).unwrap();
        let topology: Topology = raw.into_topology().into();
        topology.validate().unwrap();
    }
}
