use crate::models::Topology;
use std::collections::BTreeMap;

pub struct StakeAnalysis {
    pub gini_coefficient: f64,
    pub top_stake_holders: BTreeMap<String, u64>,
    pub total_stake: u64,
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

    StakeAnalysis {
        gini_coefficient: gini,
        top_stake_holders,
        total_stake,
    }
}
