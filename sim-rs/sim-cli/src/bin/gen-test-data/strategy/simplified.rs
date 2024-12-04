use std::time::Duration;

use anyhow::Result;
use clap::Parser;
use rand::{rngs::ThreadRng, thread_rng, Rng};
use sim_core::config::{RawLinkConfig, RawNodeConfig};

use super::utils::{distribute_stake, LinkTracker};

#[derive(Debug, Parser)]
pub struct SimplifiedArgs {
    pool_count: usize,
}

struct Cluster {
    origin: (f64, f64),
}

impl Cluster {
    fn new(lat: f64, long: f64) -> Self {
        Self {
            origin: (lat, long),
        }
    }

    fn random_loc(&self, rng: &mut ThreadRng) -> ((f64, f64), (f64, f64)) {
        let (lat_origin, long_origin) = self.origin;
        let lat_offset = rng.gen_range(-10.0..10.0);
        let long_offset = rng.gen_range(-10.0..10.0);
        let pool_loc = (
            lat_origin + lat_offset * 2.0,
            long_origin + long_offset * 2.0,
        );
        let relay_loc = (lat_origin + lat_offset, long_origin + long_offset);
        (pool_loc, relay_loc)
    }
}

const SHORT_HOP: Duration = Duration::from_millis(12);
const MEDIUM_HOP: Duration = Duration::from_millis(69);
const LONG_HOP: Duration = Duration::from_millis(268);

pub fn simplified(args: &SimplifiedArgs) -> Result<(Vec<RawNodeConfig>, Vec<RawLinkConfig>)> {
    let mut rng = thread_rng();

    let mut nodes = vec![];
    let mut links = LinkTracker::new();

    // We want nodes to have ~equal numbers of "short", "medium", and "long" connections to each other.
    // We also want physically plausible arrangements of nodes, so visualizations make sense.
    // So we generate nodes in 5 "clusters", such that every cluster has two "medium" and two "large" neighbors.
    // Then for some N, we give each node (at least) 2N connections within its cluster, and N connections to each other cluster.
    let pool_count = args.pool_count.next_multiple_of(5);
    let cluster_size = pool_count / 5;
    let clusters = [
        Cluster::new(0.0, 20.0),
        Cluster::new(40.0, 60.0),
        Cluster::new(30.0, 120.0),
        Cluster::new(-30.0, 120.0),
        Cluster::new(-40.0, 60.0),
    ];

    let relays_in_cluster = |cluster: usize| {
        (0..pool_count)
            .step_by(cluster_size * 2)
            .map(move |id| (cluster * 2) + id + 1)
    };
    let stake = distribute_stake(pool_count)?;
    for i in 0..pool_count {
        let cluster = i % 5;
        let (pool_loc, relay_loc) = clusters[cluster].random_loc(&mut rng);
        let pool_id = nodes.len();
        nodes.push(RawNodeConfig {
            location: pool_loc,
            stake: stake.get(i).cloned(),
        });
        let relay_id = nodes.len();
        nodes.push(RawNodeConfig {
            location: relay_loc,
            stake: None,
        });

        links.add(pool_id, relay_id, Some(SHORT_HOP));

        let mut local_candidates: Vec<usize> = relays_in_cluster(cluster)
            .filter(|id| *id != relay_id)
            .collect();

        // Generate at least four connections within our cluster
        for _ in 0..3 {
            if local_candidates.is_empty() {
                break;
            }
            let neighbor = local_candidates.remove(rng.gen_range(0..local_candidates.len()));
            links.add(relay_id, neighbor, Some(SHORT_HOP));
        }

        for other_cluster in (0..5).filter(|c| *c != cluster) {
            let latency =
                if cluster == (other_cluster + 1) % 5 || (cluster + 1) % 5 == other_cluster {
                    MEDIUM_HOP
                } else {
                    LONG_HOP
                };

            let mut candidates: Vec<usize> = relays_in_cluster(other_cluster).collect();

            // Generate at least two connections to other clusters
            for _ in 0..1 {
                if candidates.is_empty() {
                    break;
                }
                let neighbor = candidates.remove(rng.gen_range(0..candidates.len()));
                links.add(relay_id, neighbor, Some(latency));
            }
        }
    }

    Ok((nodes, links.links))
}
