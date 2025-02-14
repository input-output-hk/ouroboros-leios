use crate::analysis::{analyze_all_paths, reverse_topology, ShortestPathLink};
use crate::analysis::{
    analyze_network_stats, analyze_stake_distribution, basic::analyze_hop_stats,
    check_triangle_inequality,
};
use crate::models::{Severity, Topology};
use std::collections::{BTreeSet, HashMap};
use std::fmt::Write;

// NEW IMPORTS
use delta_q::{CompactionMode, StepValue, CDF};
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
        let (near, far) = get_near_far_latencies(&sp);

        eprintln!("{}", near);
        eprintln!("{}", far);
    } else {
        let reversed_topology = reverse_topology(topology);
        let mut near = CDF::bottom();
        let mut near_count = 0f32;
        let mut far = CDF::bottom();
        let mut far_count = 0f32;
        for node in reversed_topology.nodes.keys() {
            let sp = crate::analysis::shortest_paths(&reversed_topology, node);
            let (near_cdf, far_cdf) = get_near_far_latencies(&sp);
            near = near
                .choice(near_count / (near_count + 1.0), &near_cdf)
                .unwrap();
            near_count += 1.0;
            far = far.choice(far_count / (far_count + 1.0), &far_cdf).unwrap();
            far_count += 1.0;
        }

        let near2 = near.compact(CompactionMode::OverApproximate, 5);
        let near3 = near.compact(CompactionMode::UnderApproximate, 5);
        let near4 = near2.choice(0.5, &near3).unwrap();
        eprintln!("{}", plot_cdf([&near, &near2, &near3, &near4]));
        eprintln!("{}", near4);

        let far2 = far.compact(CompactionMode::OverApproximate, 5);
        let far3 = far.compact(CompactionMode::UnderApproximate, 5);
        let far4 = far2.choice(0.5, &far3).unwrap();
        eprintln!("{}", plot_cdf([&far, &far2, &far3, &far4]));
        eprintln!("{}", far4);
    }

    report
}

fn get_near_far_latencies(sp: &HashMap<String, ShortestPathLink>) -> (CDF, CDF) {
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

    // here x is node count and y is latency, so we need to turn them around
    let near = latencies[0..first_cut]
        .iter()
        .map(|&(x, y)| (y, (x + 1.0) / (first_cut as f32)))
        .collect();
    let far = latencies[second_cut + 1..]
        .iter()
        .map(|&(x, y)| {
            (
                y,
                (x - second_cut as f32) / (latencies.len() - second_cut - 1) as f32,
            )
        })
        .collect();

    (near, far)
}

fn line_point_dist(line_start: (f32, f32), line_end: (f32, f32), point: (f32, f32)) -> f32 {
    let a = line_end.0 - line_start.0;
    let b = line_end.1 - line_start.1;
    let c = point.0 - line_start.0;
    let d = point.1 - line_start.1;
    (a * d - b * c).abs() / (a * a + b * b).sqrt()
}

fn plot_cdf<'a>(cdf: impl IntoIterator<Item = &'a CDF> + 'a) -> String {
    let mut iter = cdf.into_iter().peekable();
    let mut chart = Chart::new(100, 60, 0.0, iter.peek().unwrap().width());
    let shapes = iter
        .map(|cdf| Shape::Steps(&cdf.steps().data()))
        .collect::<Vec<_>>();
    let mut chart = &mut chart;
    for shape in &shapes {
        chart = chart.lineplot(shape);
    }
    chart.axis();
    chart.figures();
    format!("{}", chart)
}
