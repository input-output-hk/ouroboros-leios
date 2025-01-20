use crate::models::{Location, Topology};
use std::collections::{BTreeMap, HashMap};

pub struct StakeAnalysis {
    pub gini_coefficient: f64,
    pub top_stake_holders: BTreeMap<String, u64>,
    pub total_stake: u64,
    pub geographic_distribution: BTreeMap<String, GeographicStake>,
}

pub struct GeographicStake {
    pub total_stake: u64,
    pub node_count: usize,
    pub percentage: f64,
}

pub fn analyze_stake_distribution(topology: &Topology) -> StakeAnalysis {
    let mut stakes: Vec<u64> = topology.nodes.iter().map(|(_, node)| node.stake).collect();
    let total_stake: u64 = stakes.iter().sum();

    // Calculate Gini coefficient
    stakes.sort();
    let n = stakes.len() as f64;
    let gini = if n > 0.0 && total_stake > 0 {
        let mut sum = 0.0;
        for (i, &stake) in stakes.iter().enumerate() {
            sum += (n - i as f64) * stake as f64;
        }
        (n + 1.0) / n - (2.0 * sum) / (n * total_stake as f64)
    } else {
        0.0
    };

    // Get top 5 stake holders
    let mut stake_holders: Vec<(String, u64)> = topology
        .nodes
        .iter()
        .map(|(name, node)| (name.clone(), node.stake))
        .collect();

    stake_holders.sort_by(|a, b| b.1.cmp(&a.1));

    let top_stake_holders: BTreeMap<String, u64> = stake_holders.into_iter().take(5).collect();

    // Calculate geographic distribution
    let mut region_stakes: HashMap<String, (u64, usize)> = HashMap::new();

    for (_, node) in topology.nodes.iter() {
        if let Location::Cluster { cluster } = &node.location {
            let region = cluster.clone().unwrap_or_else(|| "unknown".to_string());
            let entry = region_stakes.entry(region).or_insert((0, 0));
            entry.0 += node.stake;
            entry.1 += 1;
        }
    }

    let mut geographic_distribution: BTreeMap<String, GeographicStake> = BTreeMap::new();
    for (region, (stake, count)) in region_stakes {
        geographic_distribution.insert(
            region,
            GeographicStake {
                total_stake: stake,
                node_count: count,
                percentage: (stake as f64 / total_stake as f64) * 100.0,
            },
        );
    }

    StakeAnalysis {
        gini_coefficient: gini,
        top_stake_holders,
        total_stake,
        geographic_distribution,
    }
}
