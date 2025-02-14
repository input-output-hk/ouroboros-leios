use crate::analysis::{
    analyze_network_stats, analyze_stake_distribution, check_triangle_inequality,
};
use crate::analysis::{reverse_topology, ShortestPathLink};
use crate::models::{Latency, Severity, Topology};
use argmin::core::observers::ObserverMode;
use argmin::core::{CostFunction, Executor, State};
use argmin::solver::particleswarm::ParticleSwarm;
use argmin_observer_slog::SlogLogger;
use delta_q::{CompactionMode, DeltaQ, EphemeralContext, LoadUpdate, PersistentContext, CDF};
use std::collections::HashMap;
use textplots::{Chart, Plot, Shape};

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

        let mut completion = CDF::bottom();
        let mut completion_count = 0f32;

        for node in reversed_topology.nodes.keys() {
            let sp = crate::analysis::shortest_paths(&reversed_topology, node);

            let (near_cdf, far_cdf) = get_near_far_latencies(&sp);
            near = near
                .choice(near_count / (near_count + 1.0), &near_cdf)
                .unwrap();
            near_count += 1.0;
            far = far.choice(far_count / (far_count + 1.0), &far_cdf).unwrap();
            far_count += 1.0;

            let completion_cdf = get_completion_cdf(&sp);
            completion = completion
                .choice(completion_count / (completion_count + 1.0), &completion_cdf)
                .unwrap();
            completion_count += 1.0;
        }

        let near = near
            .compact(CompactionMode::OverApproximate, 10)
            .choice(0.5, &near.compact(CompactionMode::UnderApproximate, 10))
            .unwrap();

        let far = far
            .compact(CompactionMode::OverApproximate, 10)
            .choice(0.5, &far.compact(CompactionMode::UnderApproximate, 10))
            .unwrap();

        eprintln!("{completion_count}");

        let observation = CompletionModel {
            near: DeltaQ::cdf(near),
            far: DeltaQ::cdf(far),
            completion: completion.clone(),
        };

        let solver = ParticleSwarm::<Vec<f32>, f32, _>::new(
            (
                vec![0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
                vec![1.0, 1.0, 1.0, 1.0, 1.0, 1.0],
            ),
            40,
        );
        let result = Executor::new(observation.clone(), solver)
            .configure(|state| state.max_iters(100))
            .add_observer(SlogLogger::term(), ObserverMode::Always)
            .run()
            .unwrap();

        eprintln!("{}", result);

        let cdf = observation
            .eval(result.state.get_best_param().unwrap().position.as_slice())
            .unwrap();

        eprintln!("{}", plot_cdf([&completion, &cdf]));
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

fn get_completion_cdf(sp: &HashMap<String, ShortestPathLink>) -> CDF {
    let mut latencies = sp.values().map(|info| info.total).collect::<Vec<_>>();
    latencies.sort();
    let mut prev_latency = Latency::zero();
    let scale = 1.0 / (latencies.len() as f32);
    let latencies = latencies
        .into_iter()
        .enumerate()
        .rev()
        .filter_map(|(i, latency)| {
            (latency != prev_latency).then(|| {
                prev_latency = latency;
                (latency.as_f32(), (i + 1) as f32 * scale)
            })
        })
        .collect::<Vec<_>>();
    latencies.into_iter().rev().collect()
}

fn line_point_dist(line_start: (f32, f32), line_end: (f32, f32), point: (f32, f32)) -> f32 {
    let a = line_end.0 - line_start.0;
    let b = line_end.1 - line_start.1;
    let c = point.0 - line_start.0;
    let d = point.1 - line_start.1;
    (a * d - b * c).abs() / (a * a + b * b).sqrt()
}

#[allow(dead_code)]
fn plot_cdf<'a>(cdf: impl IntoIterator<Item = &'a CDF> + 'a) -> String {
    let mut iter = cdf.into_iter().peekable();
    let mut chart = Chart::new(400, 300, 0.0, iter.peek().unwrap().width());
    let shapes = iter
        .map(|cdf| Shape::Steps(&cdf.steps().data()))
        .collect::<Vec<_>>();
    for shape in &shapes {
        chart.lineplot(shape);
    }
    chart.axis();
    chart.figures();
    format!("{}", chart)
}

#[derive(Debug, Clone)]
pub struct CompletionModel {
    pub near: DeltaQ,
    pub far: DeltaQ,
    pub completion: CDF,
}

impl CompletionModel {
    pub fn eval(&self, param: &[f32]) -> Result<CDF, argmin::core::Error> {
        let near_hop0 = param[0];
        let near_hop1 = param[1];
        let near_hop2 = param[2];
        let far_hop0 = param[3];
        let far_hop1 = param[4];
        let far_hop2 = param[5];

        let expr = DeltaQ::seq(
            DeltaQ::choice(
                DeltaQ::top(),
                near_hop0,
                DeltaQ::seq(
                    self.near.clone(),
                    LoadUpdate::default(),
                    DeltaQ::choice(
                        DeltaQ::top(),
                        near_hop1,
                        DeltaQ::seq(
                            self.near.clone(),
                            LoadUpdate::default(),
                            DeltaQ::choice(
                                DeltaQ::top(),
                                near_hop2,
                                self.near.clone(),
                                1.0 - near_hop2,
                            ),
                        ),
                        1.0 - near_hop1,
                    ),
                ),
                1.0 - near_hop0,
            ),
            LoadUpdate::default(),
            DeltaQ::choice(
                DeltaQ::top(),
                far_hop0,
                DeltaQ::seq(
                    self.far.clone(),
                    LoadUpdate::default(),
                    DeltaQ::choice(
                        DeltaQ::top(),
                        far_hop1,
                        DeltaQ::seq(
                            self.far.clone(),
                            LoadUpdate::default(),
                            DeltaQ::choice(
                                DeltaQ::top(),
                                far_hop2,
                                self.far.clone(),
                                1.0 - far_hop2,
                            ),
                        ),
                        1.0 - far_hop1,
                    ),
                ),
                1.0 - far_hop0,
            ),
        );
        let ctx = PersistentContext::default();
        let mut ephemeral = EphemeralContext::default();
        Ok(expr
            .eval(&ctx, &mut ephemeral)
            .map_err(|e| argmin::core::Error::new(e))?
            .cdf)
    }
}

impl CostFunction for CompletionModel {
    type Param = Vec<f32>;
    type Output = f32;

    fn cost(&self, param: &Self::Param) -> Result<Self::Output, argmin::core::Error> {
        let result = self.eval(param)?;
        Ok(self.completion.diff_area(&result))
    }
}
