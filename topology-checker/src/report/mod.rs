use crate::analysis::{analyze_all_paths, reverse_topology, ShortestPathLink};
use crate::analysis::{
    analyze_network_stats, analyze_stake_distribution, basic::analyze_hop_stats,
    check_triangle_inequality,
};
use crate::models::{Severity, Topology};
use std::collections::{BTreeSet, HashMap};
use std::fmt::Write;

// NEW IMPORTS
use std::collections::BTreeMap;
use terminal_size::{terminal_size, Width};
use textplots::{Chart, ColorPlot, Plot, Shape};

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

    report.push_str("### Top 5 Stake Holders\n\n");
    report.push_str("| Node | Stake | % of Total |\n");
    report.push_str("|------|--------|------------|\n");
    for (node, stake) in stake_stats.top_stake_holders {
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
        report.push_str("The following nodes, if removed, would isolate significant stake:\n\n");
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
        let sp = crate::analysis::shortest_paths(&reverse_topology(topology), node);
        let mut latencies = sp.values().map(|info| info.latency).collect::<Vec<_>>();
        latencies.sort();
        let latencies = latencies
            .iter()
            .enumerate()
            .map(|(i, latency)| (i as f32, latency.as_f32()))
            .collect::<Vec<_>>();

        let line_start = latencies[0];
        let line_end = latencies[latencies.len() - 1];
        let max_dist = latencies
            .iter()
            .map(|&(x, y)| line_point_dist(line_start, line_end, (x, y)))
            .max_by(|a, b| a.total_cmp(b))
            .unwrap()
            / 1.1;
        let first_cut = latencies
            .iter()
            .position(|&(x, y)| line_point_dist(line_start, line_end, (x, y)) > max_dist)
            .unwrap();
        let second_cut = latencies
            .iter()
            .rposition(|&(x, y)| line_point_dist(line_start, line_end, (x, y)) > max_dist)
            .unwrap();

        let shape1 = Shape::Lines(&latencies[0..first_cut]);
        let shape2 = Shape::Lines(&latencies[first_cut..second_cut]);
        let shape3 = Shape::Lines(&latencies[second_cut..]);
        let mut chart = Chart::new(100, 60, 0.0, latencies.len() as f32 + 1.0);
        let chart = chart.linecolorplot(&shape1, (205, 0, 0).into());
        // let chart = chart.linecolorplot(&shape2, (0, 205, 0).into());
        let chart = chart.linecolorplot(&shape3, (0, 0, 205).into());
        chart.axis();
        chart.figures();
        eprintln!("{}", chart);

        // let sps = sp
        //     .iter()
        //     .map(|(k, v)| (v.total, k.clone()))
        //     .collect::<BTreeSet<_>>();
        // let width = get_terminal_width().unwrap_or(80) as usize - 1;
        // let max_time = sps.last().unwrap().0.as_f64();
        // for (_latency, node) in sps {
        //     report.push_str(&format_path_timeline(&sp, &node, width, max_time));
        //     report.push_str("\n");
        // }

        // let hop_stats = analyze_hop_stats(&reverse_topology(topology), node);

        // report.push_str("\n### Raw Latencies per Hop\n\n");
        // for stats in &hop_stats {
        //     report.push_str(&format!("Hop {}: CDF[", stats.hop_number));
        //     let scale = 1.0 / stats.latencies.len() as f64;
        //     let mut steps = stats
        //         .latencies
        //         .iter()
        //         .enumerate()
        //         .map(|(y_idx, x)| {
        //             (
        //                 format!("{:.3}", x),
        //                 format!("{:.3}", (y_idx + 1) as f64 * scale),
        //             )
        //         })
        //         .collect::<Vec<_>>();
        //     steps.reverse();
        //     let mut prev_x = "-1".to_owned();
        //     steps.retain(|(x, _y)| {
        //         if *x != prev_x {
        //             prev_x = x.clone();
        //             true
        //         } else {
        //             false
        //         }
        //     });
        //     for (idx, (x, y)) in steps.iter().rev().enumerate() {
        //         if idx > 0 {
        //             report.push_str(",");
        //         }
        //         report.push_str(&format!("({}, {})", x, y));
        //     }
        //     report.push_str("]\n\n");
        // }
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

pub fn get_terminal_width() -> Option<u16> {
    // terminal_size() returns an Option<(Width, Height)>
    if let Some((Width(w), _)) = terminal_size() {
        Some(w)
    } else {
        None
    }
}

// NEW FUNCTION: Format the timeline of node reaches along the shortest path.
// This function reconstructs the shortest path to `target` by following the `prev` pointers
// in the `shortest_paths` result and produces a string of length `width`.
// Each character represents a time interval (with the whole string spanning up to `max_time`).
// The time a node is reached is marked with `X`. If two node timings compute to the same
// column position, the later one is shifted to the right.
pub fn format_path_timeline(
    sp: &HashMap<String, ShortestPathLink>,
    target: &str,
    width: usize,
    max_time: f64,
) -> String {
    // Reconstruct the shortest path chain from the start to the target.
    let mut chain = Vec::new();
    let mut current = target;
    while let Some(info) = sp.get(current) {
        chain.push(info.total.as_f64());
        current = &info.node;
    }
    chain.reverse();

    // Prepare the timeline string as a vector of '-' characters.
    let mut timeline: Vec<char> = vec!['-'; width];

    // For each node in the reconstructed path, determine its column (time bucket).
    let mut pos = 0;
    for &time in &chain {
        // Compute the column index by mapping time to the width.
        pos = ((time / max_time) * (width as f64)).floor() as usize;
        if pos >= width {
            pos = width - 1;
        }
        // If the computed column is already marked, shift to the right to ensure one X per node.
        while pos < width && timeline[pos] == 'X' {
            pos += 1;
        }
        if pos >= width {
            pos = width - 1;
        }
        timeline[pos] = 'X';
    }
    for p in pos + 1..width {
        timeline[p] = ' ';
    }

    timeline.into_iter().collect()
}

fn line_point_dist(line_start: (f32, f32), line_end: (f32, f32), point: (f32, f32)) -> f32 {
    let a = line_end.0 - line_start.0;
    let b = line_end.1 - line_start.1;
    let c = point.0 - line_start.0;
    let d = point.1 - line_start.1;
    (a * d - b * c).abs() / (a * a + b * b).sqrt()
}
