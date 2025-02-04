use crate::analysis::{analyze_all_paths, reverse_topology};
use crate::analysis::{
    analyze_network_stats, analyze_stake_distribution, basic::analyze_hop_stats,
    check_triangle_inequality,
};
use crate::models::{Severity, Topology};
use std::fmt::Write;
pub fn generate_report(topology: &Topology, filename: &str, start_node: Option<&str>) -> String {
    let mut report = String::new();
    let mut issues = Vec::new();

    // Run analyses
    let network_stats = analyze_network_stats(topology);
    let stake_stats = analyze_stake_distribution(topology);
    issues.extend(check_triangle_inequality(topology));

    // Sort issues by severity and node id
    issues.sort_by_key(|issue| (-(issue.severity as i32), issue.node.clone()));

    // Generate report sections
    report.push_str("# Topology Analysis Report\n\n");
    report.push_str(&format!("Analysis of: {}\n\n", filename));

    // Add network statistics section
    report.push_str("## Network Statistics\n\n");
    report.push_str("| Metric | Value |\n");
    report.push_str("|--------|-------|\n");
    report.push_str(&format!(
        "| Total nodes | {} |\n",
        network_stats.total_nodes
    ));
    report.push_str(&format!(
        "| Block producers | {} |\n",
        network_stats.block_producers
    ));
    report.push_str(&format!(
        "| Relay nodes | {} |\n",
        network_stats.relay_nodes
    ));
    report.push_str(&format!(
        "| Total connections | {} |\n",
        network_stats.total_connections
    ));
    report.push_str(&format!(
        "| Network diameter | {} hops |\n",
        network_stats.network_diameter
    ));
    report.push_str(&format!(
        "| Average connections per node | {:.2} |\n",
        network_stats.avg_connections
    ));
    report.push_str(&format!(
        "| Clustering coefficient | {:.3} |\n",
        network_stats.clustering_coefficient
    ));
    report.push_str(&format!(
        "| Average latency | {:.2} ms |\n",
        network_stats.avg_latency_ms
    ));
    report.push_str(&format!(
        "| Maximum latency | {:.2} ms |\n",
        network_stats.max_latency_ms
    ));
    report.push_str(&format!(
        "| Stake-weighted latency | {:.2} ms |\n",
        network_stats.stake_weighted_latency_ms
    ));
    report.push_str(&format!(
        "| Bidirectional connections | {} |\n",
        network_stats.bidirectional_connections
    ));
    report.push_str(&format!(
        "| Asymmetry ratio | {:.2}% |\n\n",
        network_stats.asymmetry_ratio * 100.0
    ));

    // Add stake distribution section
    report.push_str("## Stake Distribution\n\n");
    report.push_str("| Metric | Value |\n");
    report.push_str("|--------|-------|\n");
    report.push_str(&format!("| Total stake | {} |\n", stake_stats.total_stake));
    report.push_str(&format!(
        "| Gini coefficient | {:.3} |\n\n",
        stake_stats.gini_coefficient
    ));

    report.push_str("### Top 5 Stake Holders (by % of total network stake)\n\n");
    report.push_str("| Node | Stake | % of Total |\n");
    report.push_str("|------|--------|------------|\n");
    let mut stake_holders: Vec<_> = stake_stats.top_stake_holders.into_iter().collect();
    stake_holders.sort_by(|(_node1, stake1), (_node2, stake2)| stake2.cmp(stake1));
    for (node, stake) in stake_holders.into_iter().take(5) {
        let percentage = (stake as f64 / stake_stats.total_stake as f64) * 100.0;
        report.push_str(&format!("| {} | {} | {:.2}% |\n", node, stake, percentage));
    }
    report.push_str("\n");

    report.push_str("### Geographic Stake Distribution\n\n");
    report.push_str("| Region | Nodes | Total Stake | % of Network |\n");
    report.push_str("|---------|--------|-------------|-------------|\n");
    for (region, stats) in stake_stats.geographic_distribution {
        report.push_str(&format!(
            "| {} | {} | {} | {:.2}% |\n",
            region, stats.node_count, stats.total_stake, stats.percentage
        ));
    }
    report.push_str("\n");

    // Add network reliability section
    if !network_stats.critical_nodes.is_empty() {
        report.push_str("## Network Reliability\n\n");
        report.push_str("The following nodes, if removed, would isolate the specified percentage of total network stake:\n\n");
        report.push_str("| Node | Isolated Stake | % of Total Stake |\n");
        report.push_str("|------|----------------|------------------|\n");
        for node in &network_stats.critical_nodes {
            report.push_str(&format!(
                "| {} | {} | {:.2}% |\n",
                node.node, node.isolated_stake, node.percentage_of_total
            ));
        }
        report.push_str("\n");
    }

    // Add geographic validation section
    report.push_str("## Geographic Validation\n\n");
    let geo_issues: Vec<_> = issues
        .iter()
        .filter(|i| matches!(i.severity, Severity::Error))
        .collect();

    if geo_issues.is_empty() {
        report.push_str("✅ No geographic violations found\n\n");
    } else {
        report.push_str("### Path Length Violations\n\n");
        for issue in geo_issues {
            report.push_str(&format!("❌ {}\n", issue.message));
            report.push_str(&format!("   Suggestion: {}\n\n", issue.suggestion));
        }
    }

    // Add hop analysis section if a start node is provided
    if let Some(node) = start_node {
        let hop_stats = analyze_hop_stats(&reverse_topology(topology), node);

        report.push_str("\n### Raw Latencies per Hop\n\n");
        for stats in &hop_stats {
            report.push_str(&format!("Hop {}: ", stats.hop_number));

            // Check for duplicate latencies
            let mut latency_counts = std::collections::HashMap::new();
            for &latency in &stats.latencies {
                *latency_counts.entry(format!("{:.3}", latency)).or_insert(0) += 1;
            }
            let duplicates: Vec<_> = latency_counts
                .iter()
                .filter(|(_, &count)| count > 1)
                .collect();

            if !duplicates.is_empty() {
                report.push_str("\n⚠️ Warning: Duplicate latencies found:\n");
                for (latency, count) in duplicates {
                    report.push_str(&format!("   {}ms appears {} times\n", latency, count));
                }
            }

            report.push_str("CDF[");

            // Create CDF points, handling duplicates
            let mut unique_latencies = stats.latencies.clone();
            unique_latencies.sort_by(|a, b| a.partial_cmp(b).unwrap());
            unique_latencies.dedup(); // Remove duplicates while keeping order

            let total_points = stats.latencies.len() as f64;
            let mut prev_y = 0.0;

            for (idx, latency) in unique_latencies.iter().enumerate() {
                if idx > 0 {
                    report.push_str(",");
                }
                // For each unique latency, count all points less than or equal
                let y = stats.latencies.iter().filter(|&&x| x <= *latency).count() as f64
                    / total_points;

                // Only output if this y is different from the previous one
                if y > prev_y || idx == 0 {
                    report.push_str(&format!("({:.3}, {:.3})", latency, y));
                    prev_y = y;
                }
            }
            report.push_str("]\n\n");
        }
    } else {
        let all_path_stats = analyze_all_paths(topology);
        report.push_str("## All Paths Analysis\n\n");
        report.push_str("| Hop |  Min  |  Avg  |  Max  |\n");
        report.push_str("|-----|-------|-------|-------|\n");
        for (idx, stats) in all_path_stats.iter().enumerate() {
            report.push_str(&format!(
                "| {:3} | {:5.2} | {:5.2} | {:5.2} |\n",
                idx, stats.reached_min, stats.reached_avg, stats.reached_max
            ));
        }
        report.push_str("\n");
        for (idx, stats) in all_path_stats.iter().enumerate() {
            writeln!(report, "hop{idx}_min := {}", stats.latency_min).ok();
            writeln!(report, "hop{idx}_avg := {}", stats.latency_avg).ok();
            writeln!(report, "hop{idx}_max := {}", stats.latency_max).ok();
        }
    }

    report
}
